import Towers.ClassField.LubinTate.PolynomialSurjectivity
import Towers.ClassField.LubinTate.AlgebraicConsequences

/-!
# Class Field Theory, Chapter I, Proposition 3.4: the open-ball model

This file isolates the exact analytic input in Milne's proof of Proposition
3.4.  Once the Lubin--Tate module is identified with the valuation-open unit
ball and multiplication by the uniformizer is identified with the basic
Lubin--Tate polynomial, the polynomial results and Lemma 3.3 give all the
module-theoretic conclusions.
-/

namespace Towers.CField.LTate

noncomputable section

open Polynomial
open Towers.CField.FGroups

/-- The valuation-open unit ball, viewed only as a type of points. -/
abbrev ValuationOpenBall
    {L Γ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) := {x : L // v x < 1}

/-- The coordinate data used in Milne's proof of Proposition 3.4.

For the actual Lubin--Tate module, `coord` is the identity on the underlying
open unit ball.  Keeping the module abstract makes explicit that the rest of
the proposition uses only the displayed formula for multiplication by `pi`.
-/
structure LBModel
    (A M L Γ : Type*) [CommRing A] [AddCommGroup M] [Module A M]
    [Field L] [Algebra A L] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) (pi : A) (q : ℕ) where
  coord : M ≃ ValuationOpenBall v
  coord_zero : (coord 0).1 = 0
  coord_uniformizer : ∀ x : M,
    (coord (pi • x)).1 =
      (basicLubinTate (algebraMap A L pi) q).eval (coord x).1

namespace LBModel

variable {A M L Γ : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  [Field L] [Algebra A L] [IsAlgClosed L]
  [LinearOrderedCommGroupWithZero Γ]
  {v : Valuation L Γ} {pi : A} {q : ℕ}

/-- Multiplication by the uniformizer is surjective on any open-ball model. -/
theorem uniformizer_surjective
    (model : LBModel A M L Γ v pi q)
    (hq : 1 < q) (hpi : v (algebraMap A L pi) < 1) :
    Function.Surjective fun x : M ↦ pi • x := by
  intro y
  obtain ⟨beta, hbeta, hmap⟩ :=
    lubin_preimage_valuation
      v (algebraMap A L pi) (model.coord y).1 hq hpi (model.coord y).2
  let betaBall : ValuationOpenBall v := ⟨beta, hbeta⟩
  refine ⟨model.coord.symm betaBall, ?_⟩
  apply model.coord.injective
  apply Subtype.ext
  rw [model.coord_uniformizer]
  simpa [betaBall] using hmap

/-- The first torsion kernel is exactly the root set of the basic polynomial. -/
def torsionKernelSet
    (model : LBModel A M L Γ v pi q)
    (hq : 1 < q) (hpi : v (algebraMap A L pi) < 1) :
    torsionKernel (M := M) pi 1 ≃
      (basicLubinTate (algebraMap A L pi) q).rootSet L where
  toFun x := ⟨(model.coord x.1).1, by
    rw [mem_rootSet]
    refine ⟨(basic_lubin_monic _ hq).ne_zero, ?_⟩
    have hkill : pi • (x : M) = 0 := by
      simpa only [pow_one] using mem_torsionKernel.mp x.2
    calc
      (basicLubinTate (algebraMap A L pi) q).eval
          (model.coord (x : M)).1 = (model.coord (pi • (x : M))).1 :=
        (model.coord_uniformizer (x : M)).symm
      _ = (model.coord 0).1 := by rw [hkill]
      _ = 0 := model.coord_zero⟩
  invFun x := ⟨model.coord.symm ⟨x.1,
      valuation_lubin_tate
        v (algebraMap A L pi) hq hpi (mem_rootSet.mp x.2).2⟩, by
    apply mem_torsionKernel.mpr
    simp only [pow_one]
    apply model.coord.injective
    apply Subtype.ext
    rw [model.coord_uniformizer]
    rw [model.coord.apply_symm_apply]
    exact ((mem_rootSet.mp x.2).2.trans model.coord_zero.symm)⟩
  left_inv x := by
    apply Subtype.ext
    exact model.coord.symm_apply_apply (x : M)
  right_inv x :=
    Subtype.ext (congrArg (fun z : ValuationOpenBall v => (z : L))
      (model.coord.apply_symm_apply ⟨x.1,
        valuation_lubin_tate
          v (algebraMap A L pi) hq hpi (mem_rootSet.mp x.2).2⟩))

/-- The first torsion kernel of an open-ball model has `q` elements. -/
theorem card_torsion_one
    (model : LBModel A M L Γ v pi q)
    (hq : 1 < q) (hpiVal : v (algebraMap A L pi) < 1)
    (hpi : algebraMap A L pi ≠ 0) (hq1 : ((q - 1 : ℕ) : L) ≠ 0) :
    Nat.card (torsionKernel (M := M) pi 1) = q := by
  calc
    Nat.card (torsionKernel (M := M) pi 1) =
        Nat.card ((basicLubinTate
          (algebraMap A L pi) q).rootSet L) :=
      Nat.card_congr (model.torsionKernelSet hq hpiVal)
    _ = Fintype.card ((basicLubinTate
          (algebraMap A L pi) q).rootSet L) := Nat.card_eq_fintype_card
    _ = q := card_set_lubin
      (algebraMap A L pi) hpi hq hq1

variable [FaithfulSMul A L]

/-- Every torsion level in an open-ball model has the expected cardinality. -/
theorem card_torsionKernel
    (model : LBModel A M L Γ v pi q)
    (hq : 1 < q) (hpiVal : v (algebraMap A L pi) < 1)
    (hpi : Irreducible pi) (hq1 : ((q - 1 : ℕ) : L) ≠ 0)
    (n : ℕ) :
    Nat.card (torsionKernel (M := M) pi n) = q ^ n := by
  apply torsionKernel_card (model.uniformizer_surjective hq hpiVal) q
  exact model.card_torsion_one hq hpiVal
    (by simpa using
      (FaithfulSMul.algebraMap_injective A L).ne hpi.ne_zero) hq1

variable [IsDomain A] [IsDiscreteValuationRing A]
  [Finite (A ⧸ Ideal.span {pi})]

/-- A nonzero prime quotient has more than one element. -/
theorem one_residue_card
    (hpi : Irreducible pi)
    (hresidue : Nat.card (A ⧸ Ideal.span {pi}) = q) : 1 < q := by
  letI : Nontrivial (A ⧸ Ideal.span {pi}) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (PrincipalIdealRing.isMaximal_of_irreducible hpi).ne_top
  simpa only [hresidue] using
    (Finite.one_lt_card (α := A ⧸ Ideal.span {pi}))

omit [IsAlgClosed L] in
/-- If `q` is the residue cardinality, then `q - 1` is nonzero in every
faithfully extending field. -/
theorem residue_sub_ne
    (hpi : Irreducible pi)
    (hresidue : Nat.card (A ⧸ Ideal.span {pi}) = q) :
    ((q - 1 : ℕ) : L) ≠ 0 := by
  let k := A ⧸ Ideal.span {pi}
  letI : Nontrivial k := Ideal.Quotient.nontrivial_iff.mpr
    (PrincipalIdealRing.isMaximal_of_irreducible hpi).ne_top
  letI : Fintype k := Fintype.ofFinite k
  have hq : 1 < q := one_residue_card hpi hresidue
  have hcardZero : (q : k) = 0 := by
    rw [← hresidue, Nat.card_eq_fintype_card]
    exact Nat.cast_card_eq_zero k
  intro hzero
  have hzeroA : ((q - 1 : ℕ) : A) = 0 := by
    apply FaithfulSMul.algebraMap_injective A L
    simpa using hzero
  have hzeroK : ((q - 1 : ℕ) : k) = 0 := by
    simpa using congrArg (Ideal.Quotient.mk (Ideal.span {pi})) hzeroA
  have hnegOne : (-1 : k) = 0 := by
    calc
      (-1 : k) = (q : k) - 1 := by rw [hcardZero, zero_sub]
      _ = ((q - 1 : ℕ) : k) := by
        rw [Nat.cast_sub hq.le]
        norm_num
      _ = 0 := hzeroK
  exact (neg_ne_zero.mpr one_ne_zero) hnegOne

/-- The first torsion kernel and the residue field have the same cardinality
when `q` is the residue-field cardinality. -/
theorem torsion_kernel_residue
    (model : LBModel A M L Γ v pi q)
    (hpiVal : v (algebraMap A L pi) < 1)
    (hpi : Irreducible pi)
    (hresidue : Nat.card (A ⧸ Ideal.span {pi}) = q) :
    Nat.card (torsionKernel (M := M) pi 1) =
      Nat.card (A ⧸ Ideal.span {pi}) := by
  exact (model.card_torsion_one
    (one_residue_card hpi hresidue) hpiVal
    (by simpa using
      (FaithfulSMul.algebraMap_injective A L).ne hpi.ne_zero)
    (residue_sub_ne hpi hresidue)).trans hresidue.symm

/-- The cardinality conclusion of Lemma 3.3, with all its hypotheses supplied
by the open-ball model. -/
theorem card_torsion_residue
    (model : LBModel A M L Γ v pi q)
    (hpiVal : v (algebraMap A L pi) < 1)
    (hpi : Irreducible pi)
    (hresidue : Nat.card (A ⧸ Ideal.span {pi}) = q) (n : ℕ) :
    Nat.card (torsionKernel (M := M) pi n) = q ^ n :=
  model.card_torsionKernel (one_residue_card hpi hresidue)
    hpiVal hpi (residue_sub_ne hpi hresidue) n

/-- Proposition 3.4: every torsion level is a cyclic quotient by `pi ^ n`. -/
theorem nonempty_torsion_quotient
    (model : LBModel A M L Γ v pi q)
    (hpiVal : v (algebraMap A L pi) < 1)
    (hpi : Irreducible pi)
    (hresidue : Nat.card (A ⧸ Ideal.span {pi}) = q) (n : ℕ) :
    Nonempty (torsionKernel (M := M) pi n ≃ₗ[A]
      A ⧸ Ideal.span {pi ^ n}) :=
  torsion_nonempty_quotient hpi
    (model.uniformizer_surjective
      (one_residue_card hpi hresidue) hpiVal)
    (model.torsion_kernel_residue
      hpiVal hpi hresidue) n

/-- The endomorphism-ring conclusion of Proposition 3.4 for an open-ball
model. -/
def torsionEndRing
    (model : LBModel A M L Γ v pi q)
    (hpiVal : v (algebraMap A L pi) < 1)
    (hpi : Irreducible pi)
    (hresidue : Nat.card (A ⧸ Ideal.span {pi}) = q) (n : ℕ) :
    Module.End A (torsionKernel (M := M) pi n) ≃+*
      A ⧸ Ideal.span {pi ^ n} :=
  Towers.CField.LTate.torsionEndRing hpi
    (model.uniformizer_surjective
      (one_residue_card hpi hresidue) hpiVal)
    (model.torsion_kernel_residue
      hpiVal hpi hresidue) n

/-- The automorphism-group conclusion of Proposition 3.4 for an open-ball
model. -/
def torsionAutUnits
    (model : LBModel A M L Γ v pi q)
    (hpiVal : v (algebraMap A L pi) < 1)
    (hpi : Irreducible pi)
    (hresidue : Nat.card (A ⧸ Ideal.span {pi}) = q) (n : ℕ) :
    (torsionKernel (M := M) pi n ≃ₗ[A]
      torsionKernel (M := M) pi n) ≃*
        (A ⧸ Ideal.span {pi ^ n})ˣ :=
  Towers.CField.LTate.torsionAutUnits hpi
    (model.uniformizer_surjective
      (one_residue_card hpi hresidue) hpiVal)
    (model.torsion_kernel_residue
      hpiVal hpi hresidue) n

end LBModel

end

end Towers.CField.LTate
