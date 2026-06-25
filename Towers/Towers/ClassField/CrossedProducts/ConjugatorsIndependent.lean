import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Towers.ClassField.CrossedProducts.CocycleRepresentatives


/-!
# Chapter IV, Section 3, Lemma 3.12

The Skolem--Noether representatives attached to a Galois subfield of the
correct degree form a basis of the ambient central simple algebra over that
subfield.
-/

namespace Towers.CField.CProduca

noncomputable section

universe u

variable (k L A : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  [Ring A] [Nontrivial A] [Algebra k A] [Module.Finite k A]

omit [Module.Finite k A] in
/-- Elements satisfying equation (39) for distinct Galois automorphisms are
linearly independent over the copy of `L` embedded in `A`. -/
theorem conjugators_linearIndependent
    (i : L →ₐ[k] A) (e : Gal(L/k) → Aˣ)
    (he : ∀ (sigma : Gal(L/k)) (a : L),
      (e sigma : A) * i a = i (sigma a) * (e sigma : A)) :
    letI : Module L A := i.toRingHom.toModule
    LinearIndependent L (fun sigma ↦ (e sigma : A)) := by
  letI : Module L A := i.toRingHom.toModule
  let a : L := IsGalois.normalBasis k L 1
  let f : Module.End L A :=
    { toFun x := x * i a
      map_add' := fun x y ↦ by rw [add_mul]
      map_smul' := fun r x ↦ by
        change (i r * x) * i a = i r * (x * i a)
        rw [mul_assoc] }
  have hvalues : Function.Injective (fun sigma : Gal(L/k) ↦ sigma a) := by
    intro sigma tau h
    apply (IsGalois.normalBasis k L).injective
    rw [IsGalois.normalBasis_apply sigma, IsGalois.normalBasis_apply tau]
    change sigma a = tau a
    exact h
  apply f.eigenvectors_linearIndependent' (fun sigma ↦ sigma a) hvalues
  intro sigma
  rw [Module.End.hasEigenvector_iff]
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    change (e sigma : A) * i a = i (sigma a) * (e sigma : A)
    exact he sigma a
  · exact Units.ne_zero (e sigma)

/-- Milne, Lemma IV.3.12: when `[A:k] = [L:k]²`, conjugators satisfying
equation (39) form a left `L`-basis of `A`. -/
def conjugatorBasis
    (i : L →ₐ[k] A) (e : Gal(L/k) → Aˣ)
    (he : ∀ (sigma : Gal(L/k)) (a : L),
      (e sigma : A) * i a = i (sigma a) * (e sigma : A))
    (hdim : Module.finrank k A = (Module.finrank k L) ^ 2) :
    letI : Module L A := i.toRingHom.toModule
    Module.Basis Gal(L/k) L A := by
  letI : Module L A := i.toRingHom.toModule
  letI : IsScalarTower k L A := ⟨fun r s x ↦ by
    change i (r • s) * x = r • (i s * x)
    rw [map_smul]
    exact Algebra.smul_mul_assoc r (i s) x⟩
  have hmul :
      Module.finrank k L * Module.finrank L A =
        Module.finrank k L * Module.finrank k L := by
    calc
      Module.finrank k L * Module.finrank L A = Module.finrank k A :=
        Module.finrank_mul_finrank k L A
      _ = (Module.finrank k L) ^ 2 := hdim
      _ = Module.finrank k L * Module.finrank k L := by rw [pow_two]
  have hfinrank : Module.finrank L A = Module.finrank k L :=
    Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := k) (M := L)) hmul
  exact basisOfLinearIndependentOfCardEqFinrank
    (conjugators_linearIndependent k L A i e he)
    (Fintype.card_eq_nat_card.trans <|
      (IsGalois.card_aut_eq_finrank k L).trans hfinrank.symm)

omit [Module.Finite k A] in
@[simp]
theorem conjugatorBasis_apply
    (i : L →ₐ[k] A) (e : Gal(L/k) → Aˣ)
    (he : ∀ (sigma : Gal(L/k)) (a : L),
      (e sigma : A) * i a = i (sigma a) * (e sigma : A))
    (hdim : Module.finrank k A = (Module.finrank k L) ^ 2)
    (sigma : Gal(L/k)) :
    letI : Module L A := i.toRingHom.toModule
    conjugatorBasis k L A i e he hdim sigma = (e sigma : A) := by
  letI : Module L A := i.toRingHom.toModule
  rw [conjugatorBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

section ConcreteRepresentatives

variable [IsSimpleRing A] [Algebra.IsCentral k A]

/-- Lemma IV.3.12 for the normalized Skolem--Noether representatives attached
to an embedding `L →ₐ[k] A`. -/
def galoisConjugatorBasis
    (i : L →ₐ[k] A)
    (hdim : Module.finrank k A = (Module.finrank k L) ^ 2) :
    letI : Module L A := i.toRingHom.toModule
    Module.Basis Gal(L/k) L A :=
  conjugatorBasis k L A i (galoisConjugator k L A i)
    (conjugator_mul_scalar k L A i) hdim

@[simp]
theorem galois_conjugator_basis
    (i : L →ₐ[k] A)
    (hdim : Module.finrank k A = (Module.finrank k L) ^ 2)
    (sigma : Gal(L/k)) :
    letI : Module L A := i.toRingHom.toModule
    galoisConjugatorBasis k L A i hdim sigma =
      (galoisConjugator k L A i sigma : A) :=
  conjugatorBasis_apply k L A i (galoisConjugator k L A i)
    (conjugator_mul_scalar k L A i) hdim sigma

end ConcreteRepresentatives

end

end Towers.CField.CProduca
