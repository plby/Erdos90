import Mathlib

namespace Struik

open scoped BigOperators

/-- The coordinate modulus cases in Struik's Theorem 6. -/
inductive ReplacementModulusSpec (ι : Type*) where
  | generator (i : ι)
  | ordinary (support : Finset ι)
  | leftExceptional (i j : ι)
  | rightExceptional (i j : ι)

/-- Equation (69), in the general multi-generator notation of Theorem 6. -/
def replacementModulus
    {ι : Type*} [DecidableEq ι]
    (p : ℕ) (α : ι → ℕ) :
    ReplacementModulusSpec ι → ℕ
  | .generator i => p ^ α i
  | .ordinary support => support.gcd fun i => p ^ α i
  | .leftExceptional i j =>
      Nat.gcd (p ^ (α i - 1)) (p ^ (α j - 1))
  | .rightExceptional i j =>
      if α i = α j then p ^ (α i - 1)
      else Nat.gcd (p ^ α i) (p ^ α j)

theorem replacementModulus_generator
    {ι : Type*} [DecidableEq ι]
    (p : ℕ) (α : ι → ℕ) (i : ι) :
    replacementModulus p α (.generator i) = p ^ α i :=
  rfl

theorem replacement_left_exceptional
    {ι : Type*} [DecidableEq ι]
    (p : ℕ) (α : ι → ℕ) (i j : ι) :
    replacementModulus p α (.leftExceptional i j) =
      Nat.gcd (p ^ (α i - 1)) (p ^ (α j - 1)) :=
  rfl

theorem replacement_modulus_exceptional
    {ι : Type*} [DecidableEq ι]
    (p : ℕ) (α : ι → ℕ) {i j : ι} (h : α i = α j) :
    replacementModulus p α (.rightExceptional i j) =
      p ^ (α i - 1) := by
  simp [replacementModulus, h]

theorem replacement_modulus_ne
    {ι : Type*} [DecidableEq ι]
    (p : ℕ) (α : ι → ℕ) {i j : ι} (h : α i ≠ α j) :
    replacementModulus p α (.rightExceptional i j) =
      Nat.gcd (p ^ α i) (p ^ α j) := by
  simp [replacementModulus, h]

/-- Tuples of exponents, each represented by its canonical residue. -/
abbrev ResidueCoordinates {ι : Type*} (N : ι → ℕ) :=
  ∀ i, ZMod (N i)

/-- Evaluate an ordered tuple of bounded natural exponents. -/
def orderedResidueProduct
    {ι G : Type*} [Group G]
    (generators : ι → G) {N : ι → ℕ}
    (coordinates : ResidueCoordinates N) :
    List ι → G
  | [] => 1
  | i :: l =>
      generators i ^ ZMod.val (coordinates i) *
        orderedResidueProduct generators coordinates l

/-- One triangular coordinate shear. The correction at `index` is required
to be independent of that same coordinate. -/
structure CShear
    {ι : Type*} [DecidableEq ι]
    (C : ι → Type*) [∀ i, AddCommGroup (C i)] where
  index : ι
  correction : (∀ i, C i) → C index
  correction_update :
    ∀ x y, correction (Function.update x index y) = correction x

namespace CShear

/-- A triangular shear is an equivalence, with inverse obtained by
subtracting the same correction. -/
noncomputable def equiv
    {ι : Type*} [DecidableEq ι]
    {C : ι → Type*} [∀ i, AddCommGroup (C i)]
    (S : CShear C) :
    (∀ i, C i) ≃ (∀ i, C i) where
  toFun x := Function.update x S.index (x S.index + S.correction x)
  invFun x := Function.update x S.index (x S.index - S.correction x)
  left_inv := by
    intro x
    funext i
    classical
    by_cases hi : i = S.index
    · subst i
      simp [Function.update, S.correction_update]
    · simp [Function.update, hi]
  right_inv := by
    intro x
    funext i
    classical
    by_cases hi : i = S.index
    · subst i
      simp [Function.update, S.correction_update]
    · simp [Function.update, hi]

end CShear

/-- A finite sequence of the triangular substitutions occurring in
equation (59). -/
noncomputable def coordinateChange
    {ι : Type*} [DecidableEq ι]
    {C : ι → Type*} [∀ i, AddCommGroup (C i)] :
    List (CShear C) → ((∀ i, C i) ≃ (∀ i, C i))
  | [] => Equiv.refl _
  | S :: steps => S.equiv.trans (coordinateChange steps)

/-- A finite ordered basis in which every element has one and only one
tuple of residues. This is the standard-commutator normal form imported
from Struik's earlier paper. -/
structure BNForm
    {ι G : Type*} [Group G] (N : ι → ℕ) where
  generators : ι → G
  order : List ι
  coordinates : ResidueCoordinates N ≃ G
  coordinates_apply :
    ∀ x, coordinates x =
      orderedResidueProduct generators x order

namespace BNForm

theorem exists_unique_coordinates
    {ι G : Type*} [Group G] {N : ι → ℕ}
    (B : BNForm (G := G) N) (g : G) :
    ∃! x : ResidueCoordinates N,
      orderedResidueProduct B.generators x B.order = g := by
  refine ⟨B.coordinates.symm g, ?_, ?_⟩
  · calc
      orderedResidueProduct B.generators (B.coordinates.symm g) B.order =
          B.coordinates (B.coordinates.symm g) :=
        (B.coordinates_apply _).symm
      _ = g := B.coordinates.apply_symm_apply g
  · intro x hx
    apply B.coordinates.injective
    rw [B.coordinates_apply, hx]
    simp

/-- Transport a known bounded normal form through a replacement-basis
coordinate equivalence. This is the formal content of equations (57)--(59)
and the basis-substitution argument preceding Theorem 6. -/
noncomputable def replace
    {ι G : Type*} [DecidableEq ι] [Group G] {N : ι → ℕ}
    (old : BNForm (G := G) N)
    (newGenerators : ι → G)
    (steps : List (CShear fun i => ZMod (N i)))
    (hchange :
      ∀ x,
        orderedResidueProduct newGenerators x old.order =
          orderedResidueProduct old.generators
            (coordinateChange steps x) old.order) :
    BNForm (G := G) N where
  generators := newGenerators
  order := old.order
  coordinates := (coordinateChange steps).trans old.coordinates
  coordinates_apply := by
    intro x
    change old.coordinates (coordinateChange steps x) =
      orderedResidueProduct newGenerators x old.order
    rw [old.coordinates_apply, hchange]

/-- Transport uniqueness through a supplied bounded normal form and a
supplied replacement coordinate change.

This is the final abstract transport step used by Struik's argument, not
Theorem 6 itself: its hypotheses include the normal form and the replacement
identity that an unconditional formalization of Theorem 6 must prove. -/
theorem unique_coordinates_replacement
    {ι G : Type*} [DecidableEq ι] [Group G] {N : ι → ℕ}
    (old : BNForm (G := G) N)
    (newGenerators : ι → G)
    (steps : List (CShear fun i => ZMod (N i)))
    (hchange :
      ∀ x,
        orderedResidueProduct newGenerators x old.order =
          orderedResidueProduct old.generators
            (coordinateChange steps x) old.order)
    (g : G) :
    ∃! x : ResidueCoordinates N,
      orderedResidueProduct newGenerators x old.order = g :=
  (old.replace newGenerators steps hchange).exists_unique_coordinates g

end BNForm

end Struik
