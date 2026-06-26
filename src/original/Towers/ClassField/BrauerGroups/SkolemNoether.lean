import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Finiteness.Basic
import Towers.ClassField.SimpleAlgebras.NaturalRightMul
import Towers.ClassField.BrauerGroups.MulLeftBijective


/-!
# Chapter IV, Theorem 2.10 (Skolem--Noether)

The proof first records the module-theoretic part of Milne's argument.  Two
finite-dimensional representations of a finite-dimensional simple algebra on
the same vector space are isomorphic.  We then apply this to the two actions of
`A ⊗ Bᵐᵒᵖ` on `B` induced by the given embeddings `A → B`.
-/

namespace Towers.CField.BGroups

open scoped TensorProduct

universe u

/-- A type synonym carrying the module structure pulled back along an algebra
homomorphism into an endomorphism algebra. -/
def PModule {k R V : Type u} [Field k] [Ring R] [Algebra k R]
    [AddCommGroup V] [Module k V] (_f : R →ₐ[k] Module.End k V) := V

namespace PModule

variable {k R V : Type u} [Field k] [Ring R] [Algebra k R]
  [AddCommGroup V] [Module k V] (f : R →ₐ[k] Module.End k V)

instance : AddCommGroup (PModule f) := inferInstanceAs (AddCommGroup V)

instance : Module k (PModule f) := inferInstanceAs (Module k V)

instance : Module (Module.End k V) (PModule f) :=
  inferInstanceAs (Module (Module.End k V) V)

instance : Module R (PModule f) := Module.compHom _ f.toRingHom

instance [Nontrivial V] : Nontrivial (PModule f) :=
  inferInstanceAs (Nontrivial V)

instance : IsScalarTower k R (PModule f) :=
  IsScalarTower.of_algebraMap_smul fun r x ↦ by
    change f (algebraMap k R r) x = r • x
    rw [f.commutes]
    rfl

instance [Module.Finite k V] : Module.Finite k (PModule f) :=
  inferInstanceAs (Module.Finite k V)

instance [Module.Finite k V] : Module.Finite R (PModule f) :=
  Module.Finite.of_restrictScalars_finite k R (PModule f)

/-- The identity comparison with the original vector space. -/
def toLinearEquiv : PModule f ≃ₗ[k] V := LinearEquiv.refl k V

@[simp]
theorem linearEquiv_apply (x : PModule f) : toLinearEquiv f x = x := rfl

@[simp]
theorem smul_def (r : R) (x : PModule f) : r • x = f r x := rfl

end PModule

section RepresentationUniqueness

variable (k R V : Type u) [Field k] [Ring R] [Algebra k R]
  [IsSimpleRing R] [Module.Finite k R]
  [AddCommGroup V] [Module k V] [Module.Finite k V] [Nontrivial V]

/-- The module-theoretic core of Skolem--Noether: two representations of a
finite-dimensional simple algebra on the same finite-dimensional vector space
are intertwined by a linear equivalence. -/
theorem nonempty_pullback_module
    (f g : R →ₐ[k] Module.End k V) :
    Nonempty (PModule f ≃ₗ[R] PModule g) := by
  letI : IsArtinianRing R := IsArtinianRing.of_finite k R
  letI : IsSemisimpleRing R :=
    IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr inferInstance
  have hfiso : IsIsotypic R (PModule f) := IsSimpleRing.isIsotypic R _
  have hgiso : IsIsotypic R (PModule g) := IsSimpleRing.isIsotypic R _
  obtain ⟨n, hn, S, hS, ⟨ef⟩⟩ := hfiso.linearEquiv_fun
  obtain ⟨m, hm, T, hT, ⟨eg⟩⟩ := hgiso.linearEquiv_fun
  letI : IsSimpleModule R S := hS
  letI : IsSimpleModule R T := hT
  letI : Nontrivial S := IsSimpleModule.nontrivial R S
  letI : Nontrivial T := IsSimpleModule.nontrivial R T
  letI : Module.Finite k S :=
    Module.Finite.of_injective (S.subtype.restrictScalars k) S.subtype_injective
  letI : Module.Finite k T :=
    Module.Finite.of_injective (T.subtype.restrictScalars k) T.subtype_injective
  obtain ⟨eST⟩ :=
    SAlgebr.nonempty_simple_modules (A := R) S T
  have hST : Module.finrank k S = Module.finrank k T :=
    (eST.restrictScalars k).finrank_eq
  have hfn : Module.finrank k V = n * Module.finrank k S := by
    calc
      Module.finrank k V = Module.finrank k (PModule f) :=
        (PModule.toLinearEquiv f).finrank_eq.symm
      _ = Module.finrank k (Fin n → S) := (ef.restrictScalars k).finrank_eq
      _ = n * Module.finrank k S := by
        rw [Module.finrank_pi_fintype]
        simp
  have hgm : Module.finrank k V = m * Module.finrank k T := by
    calc
      Module.finrank k V = Module.finrank k (PModule g) :=
        (PModule.toLinearEquiv g).finrank_eq.symm
      _ = Module.finrank k (Fin m → T) := (eg.restrictScalars k).finrank_eq
      _ = m * Module.finrank k T := by
        rw [Module.finrank_pi_fintype]
        simp
  have hnmul : n * Module.finrank k S = m * Module.finrank k S := by
    rw [← hfn, hgm, hST]
  have hSpos : 0 < Module.finrank k S := Module.finrank_pos
  have hnm : n = m := Nat.eq_of_mul_eq_mul_right hSpos hnmul
  subst m
  exact ⟨ef.trans ((LinearEquiv.piCongrRight fun _ ↦ eST).trans eg.symm)⟩

end RepresentationUniqueness

section SkolemNoether

variable (k A B : Type u) [Field k] [Ring A] [Ring B]
  [Algebra k A] [Algebra k B]
  [IsSimpleRing A] [IsSimpleRing B] [Algebra.IsCentral k B]
  [Module.Finite k A] [Module.Finite k B]

/-- Milne's Theorem IV.2.10 (Skolem--Noether).  Two homomorphisms from a
finite-dimensional simple algebra into a finite-dimensional central simple
algebra differ by an inner automorphism of the target. -/
theorem skolemNoether (f g : A →ₐ[k] B) :
    ∃ b : Bˣ, ∀ a : A, f a = (b : B) * g a * (b⁻¹ : Bˣ) := by
  let R := A ⊗[k] Bᵐᵒᵖ
  let F : R →ₐ[k] Module.End k B :=
    (AlgHom.mulLeftRight k B).comp
      (Algebra.TensorProduct.map f (AlgHom.id k Bᵐᵒᵖ))
  let G : R →ₐ[k] Module.End k B :=
    (AlgHom.mulLeftRight k B).comp
      (Algebra.TensorProduct.map g (AlgHom.id k Bᵐᵒᵖ))
  letI : IsSimpleRing R :=
    tensor_simple_central k A Bᵐᵒᵖ
  obtain ⟨e⟩ := nonempty_pullback_module k R B F G
  let b : B := e (show PModule F from (1 : B))
  have he_mul (x : B) : e x = b * x := by
    have h := e.map_smul (1 ⊗ₜ[k] MulOpposite.op x)
      (show PModule F from (1 : B))
    simpa [R, F, G, b, PModule.smul_def,
      AlgHom.mulLeftRight_apply] using h
  have hbij : Function.Bijective (b * · : B → B) := by
    simpa only [← he_mul] using e.bijective
  have hb : IsUnit b := IsUnit.isUnit_iff_mulLeft_bijective.mpr hbij
  let u : Bˣ := hb.unit
  have hu : (u : B) = b := hb.unit_spec
  have hintertwine (a : A) : (u : B) * f a = g a * (u : B) := by
    have h := e.map_smul (a ⊗ₜ[k] (1 : Bᵐᵒᵖ))
      (show PModule F from (1 : B))
    simpa [R, F, G, PModule.smul_def,
      AlgHom.mulLeftRight_apply, he_mul, hu] using h
  refine ⟨u⁻¹, fun a ↦ ?_⟩
  calc
    f a = (u⁻¹ : Bˣ) * ((u : B) * f a) := by simp
    _ = (u⁻¹ : Bˣ) * (g a * (u : B)) := by rw [hintertwine]
    _ = ((u⁻¹ : Bˣ) : B) * g a * (u : B) := by rw [mul_assoc]
    _ = ((u⁻¹ : Bˣ) : B) * g a * (((u⁻¹)⁻¹ : Bˣ) : B) := by simp

end SkolemNoether

end Towers.CField.BGroups
