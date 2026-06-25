import Towers.ClassField.HilbertSymbols.QuadraticHilbert

/-!
# Chapter VIII, Section 6: the concrete quadratic Hilbert indicator

The local-field proof that the quadratic Hilbert symbol is bimultiplicative and nondegenerate is
not yet available.  The elementary identities in Lemma 6.5 that depend only on its conic
description are valid over every field and are recorded here.
-/

namespace Towers.CField.QForms

open Towers.CField.HSymbol

variable {K : Type*} [Field K]

private theorem neg_unit_ne : (-1 : ℤˣ) ≠ 1 := by
  intro h
  have hval := congrArg (fun u : ℤˣ => (u : ℤ)) h
  change (-1 : ℤ) = 1 at hval
  have hne : (-1 : ℤ) ≠ 1 := by decide
  exact hne hval

private theorem ne_neg_unit : (1 : ℤˣ) ≠ -1 :=
  Ne.symm neg_unit_ne

/-- The sign attached to the quadratic conic: `1` when it has a nontrivial point and `-1`
otherwise.  Over a nonarchimedean local field this is Milne's quadratic Hilbert symbol. -/
noncomputable def quadraticHilbertSign (a b : K) : ℤˣ :=
  letI : Decidable (NontrivialQuadraticConic a b) := Classical.propDecidable _
  if NontrivialQuadraticConic a b then 1 else -1

@[simp]
theorem hilbert_sign_one (a b : K) :
    quadraticHilbertSign a b = 1 ↔ NontrivialQuadraticConic a b := by
  classical
  by_cases h : NontrivialQuadraticConic a b <;>
    simp [quadraticHilbertSign, h]

@[simp]
theorem hilbert_sign_neg (a b : K) :
    quadraticHilbertSign a b = -1 ↔ ¬ NontrivialQuadraticConic a b := by
  classical
  by_cases h : NontrivialQuadraticConic a b <;>
    simp [quadraticHilbertSign, h]

/-- Lemma 6.5(c), symmetry. -/
theorem quadratic_sign_comm (a b : K) :
    quadraticHilbertSign a b = quadraticHilbertSign b a := by
  classical
  unfold quadraticHilbertSign
  rw [nontrivial_conic_comm]

/-- Lemma 6.5(a), invariance when the first argument is multiplied by a nonzero square. -/
theorem quadratic_sign_sq (a b u : K) (hu : u ≠ 0) :
    quadraticHilbertSign (a * u ^ 2) b = quadraticHilbertSign a b := by
  classical
  unfold quadraticHilbertSign
  rw [nontrivial_quadratic_conic a b u hu]

/-- Lemma 6.5(a), invariance when the second argument is multiplied by a nonzero square. -/
theorem hilbert_sign_sq (a b u : K) (hu : u ≠ 0) :
    quadraticHilbertSign a (b * u ^ 2) = quadraticHilbertSign a b := by
  classical
  unfold quadraticHilbertSign
  rw [nontrivial_conic_sq a b u hu]

/-- Lemma 6.5(d): `(1,a)=1`. -/
@[simp]
theorem hilbert_sign_left (a : K) : quadraticHilbertSign 1 a = 1 := by
  rw [hilbert_sign_one]
  refine ⟨1, 0, 1, Or.inl one_ne_zero, ?_⟩
  simp

/-- Lemma 6.5(d): `(a,1)=1`. -/
@[simp]
theorem hilbert_sign_right (a : K) : quadraticHilbertSign a 1 = 1 := by
  rw [quadratic_sign_comm]
  exact hilbert_sign_left a

/-- Lemma 6.5(d): `(a,-a)=1`. -/
@[simp]
theorem quadratic_sign_neg (a : K) : quadraticHilbertSign a (-a) = 1 := by
  rw [hilbert_sign_one]
  refine ⟨1, 1, 0, Or.inl one_ne_zero, ?_⟩
  ring

/-- For nonsquare `a`, triviality of the sign is exactly the quadratic norm equation. -/
theorem quadratic_hilbert_sign
    {a b : K} (ha : ¬ IsSquare a) :
    quadraticHilbertSign a b = 1 ↔ QuadraticValue a b := by
  rw [hilbert_sign_one]
  exact (nontrivial_conic_solution ha).symm

end Towers.CField.QForms
