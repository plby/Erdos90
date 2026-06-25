import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
Tuple identities needed for the inhomogeneous group-cochain cup product.

The input to the differential has `r + s + 1` entries.  Its face index is
split as

* `Fin.castAdd (s + 1) j`, for `j : Fin r` (strictly before the seam), and
* `Fin.natAdd r k`, for `k : Fin (s + 1)` (at or after the seam).

The output of a face has `r + s` entries, split by `Fin.castAdd s` and
`Fin.natAdd r`.
-/

namespace Towers.CField.COps.CPBuild

open scoped BigOperators

variable {α : Type*} {r s : ℕ}

/-- The first `r + 1` entries of a tuple of length `r + s + 1`.
This is extensionally `g ∘ Fin.castAdd s`, modulo reassociation of addition. -/
def prefixSucc (g : Fin (r + s + 1) → α) : Fin (r + 1) → α :=
  fun i => g ⟨i, by omega⟩

/-- The first `r` entries of a tuple of length `r + s + 1`. -/
def prefixTuple (g : Fin (r + s + 1) → α) : Fin r → α :=
  fun i => g ⟨i, by omega⟩

/-- The last `s + 1` entries of a tuple of length `r + s + 1`. -/
def suffixSucc (g : Fin (r + s + 1) → α) : Fin (s + 1) → α :=
  g ∘ Fin.natAdd r

/-- A face index strictly before the cup-product seam. -/
def leftIndex (j : Fin r) : Fin (r + s + 1) :=
  Fin.castAdd (s + 1) j

/-- A face index at or after the seam.  `rightIndex 0` is the seam. -/
def rightIndex (k : Fin (s + 1)) : Fin (r + s + 1) :=
  Fin.natAdd r k

@[simp] lemma leftIndex_val (j : Fin r) : (leftIndex (s := s) j : ℕ) = j := rfl

@[simp] lemma rightIndex_val (k : Fin (s + 1)) :
    (rightIndex (r := r) k : ℕ) = r + k := rfl

/-- Contracting before the seam contracts the corresponding first-block tuple. -/
theorem contract_left_prefix (op : α → α → α)
    (g : Fin (r + s + 1) → α) (j : Fin r) :
    Fin.contractNth (leftIndex (s := s) j) op g ∘ Fin.castAdd s =
      Fin.contractNth j.castSucc op (prefixSucc g) := by
  funext i
  simp only [Function.comp_apply]
  rcases lt_trichotomy (i : ℕ) j with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ h,
      Fin.contractNth_apply_of_lt _ _ _ _ h]
    rfl
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ h,
      Fin.contractNth_apply_of_eq _ _ _ _ h]
    rfl
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ h,
      Fin.contractNth_apply_of_gt _ _ _ _ h]
    rfl

/-- Contracting before the seam shifts the untouched second block by one. -/
theorem contract_left_suffix (op : α → α → α)
    (g : Fin (r + s + 1) → α) (j : Fin r) :
    Fin.contractNth (leftIndex (s := s) j) op g ∘ Fin.natAdd r =
      fun i : Fin s => g ⟨r + 1 + i, by omega⟩ := by
  funext i
  simp only [Function.comp_apply]
  rw [Fin.contractNth_apply_of_gt]
  · congr 1
    apply Fin.ext
    simp only [Fin.val_succ, Fin.natAdd]
    omega
  · change (j : ℕ) < r + (i : ℕ)
    omega

/-- Contracting at or after the seam leaves the first block unchanged. -/
theorem contract_right_prefix (op : α → α → α)
    (g : Fin (r + s + 1) → α) (k : Fin (s + 1)) :
    Fin.contractNth (rightIndex (r := r) k) op g ∘ Fin.castAdd s = prefixTuple g := by
  funext i
  simp only [Function.comp_apply]
  rw [Fin.contractNth_apply_of_lt]
  · rfl
  · change (i : ℕ) < r + (k : ℕ)
    omega

/-- Contracting at or after the seam contracts the corresponding second-block tuple. -/
theorem contract_right_suffix (op : α → α → α)
    (g : Fin (r + s + 1) → α) (k : Fin (s + 1)) :
    Fin.contractNth (rightIndex (r := r) k) op g ∘ Fin.natAdd r =
      Fin.contractNth k op (suffixSucc g) := by
  funext i
  simp only [Function.comp_apply]
  rcases lt_trichotomy (i : ℕ) k with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ h,
      Fin.contractNth_apply_of_lt _ _ _ _ (by simpa [rightIndex] using add_lt_add_left h r)]
    rfl
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ h,
      Fin.contractNth_apply_of_eq _ _ _ _ (by simpa [rightIndex] using congrArg (r + ·) h)]
    rfl
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ h,
      Fin.contractNth_apply_of_gt _ _ _ _ (by simpa [rightIndex] using add_lt_add_left h r)]
    rfl

/-- The seam is the zeroth face of the second block. -/
theorem contract_seam_suffix (op : α → α → α)
    (g : Fin (r + s + 1) → α) :
    Fin.contractNth (rightIndex (r := r) (0 : Fin (s + 1))) op g ∘ Fin.natAdd r =
      Fin.contractNth 0 op (suffixSucc g) :=
  contract_right_suffix op g 0

/-- A face strictly after the seam is the corresponding positive face of the second block. -/
theorem contract_after_seam (op : α → α → α)
    (g : Fin (r + s + 1) → α) (j : Fin s) :
    Fin.contractNth (rightIndex (r := r) j.succ) op g ∘ Fin.natAdd r =
      Fin.contractNth j.succ op (suffixSucc g) :=
  contract_right_suffix op g j.succ

section PrefixProducts

variable {G : Type*} [Monoid G]

/-- The boundary after the first `r` entries of a tuple of length `r + s`. -/
def prefixBoundary : Fin (r + s + 1) := ⟨r, by omega⟩

/-- The boundary after the first `r + 1` entries of a tuple of length `r + s + 1`. -/
def prefixBoundarySucc : Fin (r + s + 2) := ⟨r + 1, by omega⟩

/-- The boundary after the first `r` entries of a tuple of length `r + s + 1`. -/
def prefixBoundaryCast : Fin (r + s + 2) := ⟨r, by omega⟩

/-- Before-seam contraction preserves the product of the first `r + 1` original entries. -/
theorem partial_contract_left (g : Fin (r + s + 1) → G) (j : Fin r) :
    Fin.partialProd (Fin.contractNth (leftIndex (s := s) j) (· * ·) g)
        (prefixBoundary (r := r) (s := s)) =
      Fin.partialProd g (prefixBoundarySucc (r := r) (s := s)) := by
  rw [Fin.partialProd_contractNth]
  simp only [Function.comp_apply]
  rw [Fin.succAbove_of_le_castSucc]
  · rfl
  · apply Fin.le_iff_val_le_val.mpr
    simp only [Fin.val_succ, leftIndex_val, Fin.val_castSucc, prefixBoundary]
    omega

/-- At-or-after-seam contraction leaves the product of the first `r` entries unchanged. -/
theorem partial_contract_right (g : Fin (r + s + 1) → G) (k : Fin (s + 1)) :
    Fin.partialProd (Fin.contractNth (rightIndex (r := r) k) (· * ·) g)
        (prefixBoundary (r := r) (s := s)) =
      Fin.partialProd g (prefixBoundaryCast (r := r) (s := s)) := by
  rw [Fin.partialProd_contractNth]
  simp only [Function.comp_apply]
  rw [Fin.succAbove_of_castSucc_lt]
  · rfl
  · apply Fin.lt_def.mpr
    simp only [Fin.val_castSucc, prefixBoundary, Fin.val_succ, rightIndex_val]
    omega

end PrefixProducts

section SumsAndSigns

variable {A : Type*} [AddCommMonoid A]

/-- Split a sum of face terms into faces before the seam and faces at/after it. -/
theorem sum_faces_two (f : Fin (r + s + 1) → A) :
    (∑ j, f j) =
      (∑ j : Fin r, f (leftIndex (s := s) j)) +
        ∑ k : Fin (s + 1), f (rightIndex (r := r) k) := by
  simpa [leftIndex, rightIndex] using
    (Fin.sum_univ_add (a := r) (b := s + 1) f)

/-- Split a sum of face terms into before, at, and strictly after the seam. -/
theorem sum_faces_three (f : Fin (r + s + 1) → A) :
    (∑ j, f j) =
      (∑ j : Fin r, f (leftIndex (s := s) j)) +
        f (rightIndex (r := r) 0) +
          ∑ j : Fin s, f (rightIndex (r := r) j.succ) := by
  rw [sum_faces_two]
  rw [Fin.sum_univ_succ]
  ac_rfl

end SumsAndSigns

section Signs

variable {R : Type*} [CommRing R]

/-- The sign of an at/after-seam face factors into the global cup sign and
the sign of the corresponding face of the second cochain. -/
theorem neg_right_index (k : Fin (s + 1)) :
    (-1 : R) ^ ((rightIndex (r := r) k : ℕ) + 1) =
      (-1 : R) ^ r * (-1 : R) ^ ((k : ℕ) + 1) := by
  rw [← pow_add]
  congr 1

/-- The last face of the first differential cancels the action term of the
second differential after multiplication by the Koszul sign. -/
theorem neg_succ_self :
    (-1 : R) ^ (r + 1) + (-1 : R) ^ r = 0 := by
  rw [pow_succ]
  simp

end Signs

end Towers.CField.COps.CPBuild
