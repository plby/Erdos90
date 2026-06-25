import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.RepresentationTheory.Character
import Submission.ClassField.Characters.DirichletCharacters
import Submission.ClassField.DirichletSeries.DirichletSeries

/-!
# Chapter VI, Section 1, Example 1.1

The classical Riemann and Dirichlet `L`-series Euler products are already
proved in Mathlib.  The Dedekind zeta function is available as the Dirichlet
series whose `n`th coefficient counts integral ideals of absolute norm `n`.

For part (e), this file records the representation, its trace character, and
the conjugacy invariance of both trace and characteristic polynomial.  These
are the algebraic ingredients needed to attach a local polynomial to an
unramified Frobenius conjugacy class.

Mathlib does not currently package the Euler product for Dedekind zeta, ray
class characters over an arbitrary number field, Hecke characters on the
idele class group, or Artin `L`-series.  Consequently the corresponding
infinite products in parts (b)--(e) are not asserted here.
-/

namespace Submission.CField.DSeries

open Filter Nat NumberField Topology
open scoped LSeries.notation

noncomputable section

/-! ## Example 1.1(a): the Riemann zeta function -/

/-- On its half-plane of convergence, the Dirichlet series with constant
coefficient one is the Riemann zeta function. -/
theorem riemann_zeta_dirichlet {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun _ : ℕ ↦ (1 : ℂ)) s = riemannZeta s :=
  LSeries_one_eq_riemannZeta hs

/-- The Euler product in Example 1.1(a). -/
theorem zeta_eulerProduct {s : ℂ} (hs : 1 < s.re) :
    Tendsto
      (fun n : ℕ ↦ ∏ p ∈ primesBelow n, (1 - (p : ℂ) ^ (-s))⁻¹)
      atTop (nhds (riemannZeta s)) :=
  riemannZeta_eulerProduct hs

/-! ## Example 1.1(b): the Dedekind zeta function -/

/-- The coefficient in the Dedekind zeta Dirichlet series counts integral
ideals of the prescribed absolute norm. -/
abbrev idealCountNorm (K : Type*) [Field K] [NumberField K] (n : ℕ) : ℂ :=
  Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

/-- Example 1.1(b), in the exact coefficient-series form used by Mathlib. -/
theorem dedekind_zeta_dirichlet
    (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    dedekindZeta K s = LSeries (idealCountNorm K) s :=
  rfl

/-! ## Example 1.1(c): classical Dirichlet characters -/

/-- The classical Dirichlet `L`-series attached to a character modulo `m`. -/
theorem dirichlet_l_euler {m : ℕ}
    (χ : DirichletCharacter ℂ m) {s : ℂ} (hs : 1 < s.re) :
    Tendsto
      (fun n : ℕ ↦ ∏ p ∈ primesBelow n,
        (1 - χ p * (p : ℂ) ^ (-s))⁻¹)
      atTop (nhds (L ↗χ s)) :=
  χ.LSeries_eulerProduct hs

/-! ## Example 1.1(e): finite-dimensional representations -/

section Representation

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
/-- The trace used in Example 1.1(e) is Mathlib's character of a
representation. -/
theorem trace_eq_character (ρ : Representation ℂ G V) (g : G) :
    Representation.character ρ g = LinearMap.trace ℂ V (ρ g) :=
  rfl

omit [FiniteDimensional ℂ V] in
/-- A group element acts through a linear equivalence. -/
def representationLinearEquiv (ρ : Representation ℂ G V) (g : G) : V ≃ₗ[ℂ] V where
  toLinearMap := ρ g
  invFun := ρ g⁻¹
  left_inv := Representation.inv_self_apply ρ g
  right_inv := Representation.self_inv_apply ρ g

omit [FiniteDimensional ℂ V] in
/-- The trace of a representation depends only on the conjugacy class. -/
theorem character_conj (ρ : Representation ℂ G V) (g h : G) :
    ρ.character (h * g * h⁻¹) = ρ.character g := by
  calc
    ρ.character (h * g * h⁻¹) = ρ.character (h * (g * h⁻¹)) := by rw [mul_assoc]
    _ = ρ.character ((g * h⁻¹) * h) := ρ.char_mul_comm (g * h⁻¹) h
    _ = ρ.character g := by simp

/-- The characteristic polynomial of the representing endomorphism depends
only on the conjugacy class. -/
theorem charpoly_conj (ρ : Representation ℂ G V) (g h : G) :
    (ρ (h * g * h⁻¹)).charpoly = (ρ g).charpoly := by
  rw [← (representationLinearEquiv ρ h).charpoly_conj (ρ g)]
  congr 1
  ext x
  simp [representationLinearEquiv, LinearEquiv.conj_apply_apply, ← Module.End.mul_apply,
    ← map_mul, mul_assoc]

/-- Milne's polynomial `P_g(T) = det(1 - ρ(g)T)`.  Reversing the usual
monic characteristic polynomial puts its leading coefficient at the
constant term, giving precisely this convention. -/
def artinPolynomial (ρ : Representation ℂ G V) (g : G) : Polynomial ℂ :=
  (ρ g).charpoly.reverse

/-- The local polynomial used to define an Artin Euler factor depends only
on the conjugacy class of the chosen Frobenius element. -/
theorem artinPolynomial_conj (ρ : Representation ℂ G V) (g h : G) :
    artinPolynomial ρ (h * g * h⁻¹) = artinPolynomial ρ g := by
  simp only [artinPolynomial, charpoly_conj ρ g h]

end Representation

end

end Submission.CField.DSeries
