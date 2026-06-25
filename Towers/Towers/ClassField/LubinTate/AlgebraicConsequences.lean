import Mathlib.Algebra.Algebra.Tower
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Towers.ClassField.LubinTate.TorsionKernel

/-!
# Class Field Theory, Chapter I, Proposition 3.4: algebraic consequences

The analytic identification of Lubin--Tate torsion with the kernel modules is
still separate.  This file proves the algebraic consequences used at the end
of Proposition 3.4: the endomorphism ring and automorphism group of a cyclic
quotient module, both abstractly and for the torsion kernels of Lemma 3.3.
-/

namespace Towers.CField.LTate

noncomputable section

/-- Every `A`-linear endomorphism of `A / I` is multiplication by a unique
element of `A / I`. -/
def quotientEndAlg
    (A : Type*) [CommRing A] (I : Ideal A) :
    (A ⧸ I) ≃ₐ[A] Module.End A (A ⧸ I) := by
  let f : (A ⧸ I) →ₐ[A] Module.End A (A ⧸ I) :=
    Algebra.lsmul A A (A ⧸ I)
  apply AlgEquiv.ofBijective f
  constructor
  · intro x y hxy
    have h := LinearMap.congr_fun hxy 1
    simpa [f] using h
  · intro g
    refine ⟨g 1, ?_⟩
    apply LinearMap.ext
    intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    dsimp [f]
    change g 1 * Ideal.Quotient.mk I a = g (Ideal.Quotient.mk I a)
    rw [show Ideal.Quotient.mk I a = a • (1 : A ⧸ I) by
      simp [Algebra.smul_def]]
    rw [map_smul]
    simp [mul_comm]

/-- Transport the quotient endomorphism calculation across a linear
equivalence with a cyclic quotient. -/
def endRingQuotient
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (e : M ≃ₗ[A] A ⧸ I) :
    Module.End A M ≃+* (A ⧸ I) :=
  (LinearEquiv.conjRingEquiv e).trans
    (quotientEndAlg A I).symm.toRingEquiv

/-- Transporting units in the endomorphism ring identifies module
automorphisms with the units of the cyclic quotient. -/
def autGroupUnits
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (e : M ≃ₗ[A] A ⧸ I) :
    (M ≃ₗ[A] M) ≃* (A ⧸ I)ˣ :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv A M).symm.trans
    (Units.mapEquiv (endRingQuotient I e).toMulEquiv)

/-- Lemma 3.3 and the cyclic-quotient calculation identify the endomorphism
ring of the `n`-th torsion kernel with `A/(pi^n)`. -/
def torsionEndRing
    {A M : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [AddCommGroup M] [Module A M]
    {pi : A} (hpi : Irreducible pi) [Finite (A ⧸ Ideal.span {pi})]
    (hsurj : Function.Surjective fun x : M ↦ pi • x)
    (hcard : Nat.card (torsionKernel (M := M) pi 1) =
      Nat.card (A ⧸ Ideal.span {pi})) (n : ℕ) :
    Module.End A (torsionKernel (M := M) pi n) ≃+*
      A ⧸ Ideal.span {pi ^ n} :=
  endRingQuotient _
    (Classical.choice
      (torsion_nonempty_quotient hpi hsurj hcard n))

/-- Under the same hypotheses, automorphisms of the `n`-th torsion kernel
are the units of `A/(pi^n)`. -/
def torsionAutUnits
    {A M : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [AddCommGroup M] [Module A M]
    {pi : A} (hpi : Irreducible pi) [Finite (A ⧸ Ideal.span {pi})]
    (hsurj : Function.Surjective fun x : M ↦ pi • x)
    (hcard : Nat.card (torsionKernel (M := M) pi 1) =
      Nat.card (A ⧸ Ideal.span {pi})) (n : ℕ) :
    (torsionKernel (M := M) pi n ≃ₗ[A]
      torsionKernel (M := M) pi n) ≃*
        (A ⧸ Ideal.span {pi ^ n})ˣ :=
  autGroupUnits _
    (Classical.choice
      (torsion_nonempty_quotient hpi hsurj hcard n))

end

end Towers.CField.LTate
