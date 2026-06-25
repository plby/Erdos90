import Towers.NumberTheory.Quadratic.FormToIdeal
import Towers.NumberTheory.Quadratic.IdealNormForms
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-!
# Milne, Algebraic Number Theory, Theorem 4.29: the ideal class of a form

This file connects the explicit form-to-ideal construction in `FormToIdeal` with ideals in the
ring of integers of a quadratic number field.  The lattice `Z a + Z (omega + r)` has index
`|a|`; for `a > 0` its absolute norm is therefore `a`.  Transporting its evident ordered basis
through an equivalence from the quadratic order to the ring of integers gives an ideal whose
normalized ideal norm form is exactly the original binary quadratic form.
-/

namespace Towers.NumberTheory.Milne

open scoped NumberField QuadraticAlgebra
open Module

noncomputable section

namespace BQForm

variable {A B : ℤ}

/-- The absolute norm of the explicit form ideal is the absolute value of its leading
coefficient. -/
theorem abs_lattice_ideal (a r c : ℤ)
    (hrel : r ^ 2 + B * r - A = a * c)
    (ha : a ≠ 0)
    [NoZeroDivisors (QOrd A B)]
    [IsDedekindDomain (QOrd A B)] :
    Ideal.absNorm (latticeIdeal A B a r c hrel) = a.natAbs := by
  let R := QOrd A B
  let I : Ideal R := latticeIdeal A B a r c hrel
  let bR : Basis (Fin 2) ℤ R := QuadraticAlgebra.basis A B
  let bI : Basis (Fin 2) ℤ I := latticeBasis A B a r c hrel ha
  rw [← Ideal.natAbs_det_basis_change bR I bI]
  congr 1
  rw [Basis.det_apply, Matrix.det_fin_two]
  simp [Basis.toMatrix_apply, bR, bI, I, R, Function.comp_def,
    QuadraticAlgebra.basis_repr_apply]

/-- With positive leading coefficient, the form ideal has absolute norm equal to that
coefficient. -/
theorem abs_ideal_pos (Q : BQForm) (r : ℤ)
    (hb : Q.b = B + 2 * r) (hdisc : Q.discriminant = B ^ 2 + 4 * A)
    (ha : 0 < Q.a) [NoZeroDivisors (QOrd A B)]
    [IsDedekindDomain (QOrd A B)] :
    Ideal.absNorm (Q.toIdeal r hb hdisc) = Q.a := by
  rw [toIdeal, abs_lattice_ideal _ _ _ _ ha.ne']
  exact Int.natAbs_of_nonneg ha.le

/-- Transport an ideal through a ring equivalence, as a `Z`-linear equivalence of the
underlying ideal lattices. -/
def idealLinearEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) : I ≃ₗ[ℤ] I.map e where
  toFun x := ⟨e x, Ideal.mem_map_of_mem e x.property⟩
  invFun y := ⟨e.symm y, Ideal.symm_apply_mem_of_equiv_iff.mpr y.property⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x
  right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y
  map_add' x y := by apply Subtype.ext; exact e.map_add x y
  map_smul' n x := by
    apply Subtype.ext
    simp only [RingHom.id_apply, Submodule.coe_smul_of_tower]
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    simp

@[simp]
theorem ideal_linear_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) (x : I) :
    (idealLinearEquiv e I x : S) = e x :=
  rfl

/-- The integral ideal obtained by transporting the explicit form ideal to the ring of
integers. -/
def mappedFormIdeal {K : Type*} [Field K] [NumberField K]
    (e : QOrd A B ≃+* 𝓞 K) (Q : BQForm) (r : ℤ)
    (hb : Q.b = B + 2 * r) (hdisc : Q.discriminant = B ^ 2 + 4 * A) :
    Ideal (𝓞 K) :=
  (Q.toIdeal r hb hdisc).map e

/-- The evident basis of a form ideal, transported to the ring of integers. -/
def mappedIdealBasis {K : Type*} [Field K] [NumberField K]
    (e : QOrd A B ≃+* 𝓞 K) (Q : BQForm) (r : ℤ)
    (hb : Q.b = B + 2 * r) (hdisc : Q.discriminant = B ^ 2 + 4 * A)
    (ha : Q.a ≠ 0) :
    Basis (Fin 2) ℤ (mappedFormIdeal e Q r hb hdisc) :=
  (Q.toIdealBasis r hb hdisc ha).map
    (idealLinearEquiv e (Q.toIdeal r hb hdisc))

@[simp]
theorem mapped_form_ideal {K : Type*} [Field K] [NumberField K]
    (e : QOrd A B ≃+* 𝓞 K) (Q : BQForm) (r : ℤ)
    (hb : Q.b = B + 2 * r) (hdisc : Q.discriminant = B ^ 2 + 4 * A)
    (ha : Q.a ≠ 0) (i : Fin 2) :
    (mappedIdealBasis e Q r hb hdisc ha i : 𝓞 K) =
      e (Q.toIdealBasis r hb hdisc ha i : QOrd A B) := by
  rw [mappedIdealBasis, Basis.map_apply]
  rfl

/-- Absolute norm is invariant under transport by a ring equivalence. -/
theorem abs_ring_equiv
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Module.Free ℤ R] [Module.Free ℤ S]
    (e : R ≃+* S) (I : Ideal R) :
    Ideal.absNorm (I.map e) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply,
    Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr
    (Ideal.quotientEquiv I (I.map e) e rfl).toEquiv.symm

/-- The transported ideal has norm equal to the positive leading coefficient. -/
theorem abs_mapped_pos {K : Type*} [Field K] [NumberField K]
    (e : QOrd A B ≃+* 𝓞 K) (Q : BQForm) (r : ℤ)
    (hb : Q.b = B + 2 * r) (hdisc : Q.discriminant = B ^ 2 + 4 * A)
    (ha : 0 < Q.a) [NoZeroDivisors (QOrd A B)]
    [IsDedekindDomain (QOrd A B)] :
    Ideal.absNorm (mappedFormIdeal e Q r hb hdisc) = Q.a := by
  rw [mappedFormIdeal, abs_ring_equiv]
  exact Q.abs_ideal_pos r hb hdisc ha

/-- Under an equivalence with a ring of integers, the algebra norm is the concrete quadratic
algebra norm. -/
theorem algebra_quadratic_order {K : Type*} [Field K] [NumberField K]
    (e : QOrd A B ≃+* 𝓞 K) (z : QOrd A B) :
    Algebra.norm ℤ (e z) = QuadraticAlgebra.norm z := by
  let eAlg : QOrd A B ≃ₐ[ℤ] 𝓞 K :=
    AlgEquiv.ofRingEquiv (f := e) (fun n => by simp)
  calc
    Algebra.norm ℤ (e z) = Algebra.norm ℤ z := by
      exact Algebra.norm_eq_of_algEquiv eAlg z
    _ = QuadraticAlgebra.norm z := by
      rw [Algebra.norm_apply]
      have hmap :
          (Algebra.lmul ℤ (QOrd A B)) z =
            DistribSMul.toLinearMap ℤ (QOrd A B) z := by
        apply LinearMap.ext
        intro x
        simp only [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply',
          DistribSMul.toLinearMap_apply, smul_eq_mul]
      rw [hmap, QuadraticAlgebra.det_toLinearMap_eq_norm]

/-- **Theorem 4.29, explicit inverse calculation.**  Transport the ideal attached to a form
to the ring of integers.  On its evident ordered basis, the normalized ideal norm form is the
original form. -/
theorem form_basis_mapped {K : Type*} [Field K] [NumberField K]
    (e : QOrd A B ≃+* 𝓞 K) (BO : Basis (Fin 2) ℤ (𝓞 K))
    (Q : BQForm) (r : ℤ)
    (hb : Q.b = B + 2 * r) (hdisc : Q.discriminant = B ^ 2 + 4 * A)
    (ha : 0 < Q.a) [NoZeroDivisors (QOrd A B)]
    [IsDedekindDomain (QOrd A B)] :
    INForm.formOfBasis (mappedFormIdeal e Q r hb hdisc)
        (mappedIdealBasis e Q r hb hdisc ha.ne') = Q := by
  let J := mappedFormIdeal e Q r hb hdisc
  let b := mappedIdealBasis e Q r hb hdisc ha.ne'
  have hnorm : Ideal.absNorm J = Q.a :=
    abs_mapped_pos e Q r hb hdisc ha
  have hJ : J ≠ ⊥ := by
    intro hJ
    rw [hJ, Ideal.absNorm_bot] at hnorm
    omega
  have hcomb (x y : ℤ) :
      x • (b 0 : 𝓞 K) + y • (b 1 : 𝓞 K) =
        e (x • (Q.a : QOrd A B) +
          y • (ω + (r : QOrd A B))) := by
    have h0 :
        ((Q.toIdealBasis r hb hdisc ha.ne' 0 : Q.toIdeal r hb hdisc) :
            QOrd A B) = (Q.a : QOrd A B) :=
      lattice_basis_coe A B Q.a r Q.c (Q.lattice_relation r hb hdisc) ha.ne'
    have h1 :
        ((Q.toIdealBasis r hb hdisc ha.ne' 1 : Q.toIdeal r hb hdisc) :
            QOrd A B) = ω + (r : QOrd A B) :=
      lattice_one_coe A B Q.a r Q.c (Q.lattice_relation r hb hdisc) ha.ne'
    rw [show (b 0 : 𝓞 K) = e
        (Q.toIdealBasis r hb hdisc ha.ne' 0 : QOrd A B) by
      exact mapped_form_ideal e Q r hb hdisc ha.ne' 0,
      show (b 1 : 𝓞 K) = e
        (Q.toIdealBasis r hb hdisc ha.ne' 1 : QOrd A B) by
      exact mapped_form_ideal e Q r hb hdisc ha.ne' 1,
      h0, h1]
    simp
  have heval (x y : ℤ) :
      (INForm.formOfBasis J b).eval x y = Q.eval x y := by
    have h := INForm.eval_form BO hJ (b 0) (b 1) x y
    change (INForm.formOfBasis J b).eval x y = _ at h
    rw [h, hcomb]
    change Algebra.norm ℤ
        (e (x • (Q.a : QOrd A B) +
          y • (ω + (r : QOrd A B)))) / (Ideal.absNorm J : ℤ) = _
    rw [algebra_quadratic_order, hnorm]
    exact Q.normal_evide_gener r hb hdisc ha.ne' x y
  change INForm.formOfBasis J b = Q
  apply BQForm.ext
  · simpa [BQForm.eval] using heval 1 0
  · have h11 := heval 1 1
    have h10 := heval 1 0
    have h01 := heval 0 1
    simp only [BQForm.eval] at h11 h10 h01 ⊢
    linarith
  · simpa [BQForm.eval] using heval 0 1

end BQForm

end

end Towers.NumberTheory.Milne
