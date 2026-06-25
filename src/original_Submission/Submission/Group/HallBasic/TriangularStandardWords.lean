import Submission.Group.HallBasic.Weight

noncomputable section

namespace Submission
namespace TBluepr

universe u v

/--
A signed triangular family of finitely supported vectors is linearly
independent.  This is the form used by a leading-word Hall argument: later
vectors vanish at the distinguished word of every earlier vector.
-/
theorem finsupp_independent_pivot
    (R : Type u) [Ring R]
    {ι : Type v} [LinearOrder ι]
    {κ : Type*}
    (vector : ι → κ →₀ R)
    (pivot : ι → κ)
    (hdiagonal :
      ∀ i, vector i (pivot i) = 1 ∨ vector i (pivot i) = -1)
    (hlater :
      ∀ i j, i < j → vector j (pivot i) = 0) :
    LinearIndependent R vector := by
  classical
  apply linearIndependent_iff'.2
  intro s coefficient hsum i hi
  by_contra hiCoefficient
  let active := s.filter fun j => coefficient j ≠ 0
  have hactive : active.Nonempty :=
    ⟨i, Finset.mem_filter.mpr ⟨hi, hiCoefficient⟩⟩
  let k := active.min' hactive
  have hkActive : k ∈ active := active.min'_mem hactive
  have hkMem : k ∈ s := (Finset.mem_filter.mp hkActive).1
  have hkCoefficient : coefficient k ≠ 0 :=
    (Finset.mem_filter.mp hkActive).2
  have hcoefficient :=
    congrArg (fun p : κ →₀ R => p (pivot k)) hsum
  change (∑ j ∈ s, coefficient j • vector j) (pivot k) = 0 at hcoefficient
  rw [Finset.sum_apply', Finset.sum_eq_single k] at hcoefficient
  · rcases hdiagonal k with hdiagonal | hdiagonal
    · exact hkCoefficient (by simpa [hdiagonal] using hcoefficient)
    · exact hkCoefficient (by simpa [hdiagonal] using hcoefficient)
  · intro j hjMem hjk
    by_cases hjActive : j ∈ active
    · have hkj : k < j :=
        lt_of_le_of_ne (active.min'_le j hjActive) hjk.symm
      simp [hlater k j hkj]
    · have hjCoefficient : coefficient j = 0 := by
        by_contra hjCoefficient
        exact hjActive (Finset.mem_filter.mpr ⟨hjMem, hjCoefficient⟩)
      simp [hjCoefficient]
  · exact fun hkNotMem => (hkNotMem hkMem).elim

/--
The triangular order may be supplied by an injective natural-number rank
rather than by an ambient order on the vector index type.
-/
theorem finsupp_triangular_pivot
    (R : Type u) [Ring R]
    {ι : Type v}
    {κ : Type*}
    (vector : ι → κ →₀ R)
    (pivot : ι → κ)
    (rank : ι → ℕ)
    (hrank : Function.Injective rank)
    (hdiagonal :
      ∀ i, vector i (pivot i) = 1 ∨ vector i (pivot i) = -1)
    (hlater :
      ∀ i j, rank i < rank j → vector j (pivot i) = 0) :
    LinearIndependent R vector := by
  letI : LinearOrder ι := LinearOrder.lift' rank hrank
  exact
    finsupp_independent_pivot
      R vector pivot hdiagonal hlater

end TBluepr

namespace HallTree

open TBluepr

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/--
A fixed-weight signed leading-word certificate for Hall polynomials.  Unlike
`SSPivots`, this records the triangular vanishing supplied by
the classical Hall leading-word proof rather than demanding complete
off-diagonal vanishing.
-/
structure STWords
    (R : Type*) [CommRing R]
    (r : ℕ) where
  standardWord : BasicIndex (α := α) r → FreeMonoid α
  rank : BasicIndex (α := α) r → ℕ
  rank_injective : Function.Injective rank
  diagonal :
    ∀ i,
      (indexedBasicTree i).associativeWordPolynomial R (standardWord i) = 1 ∨
        (indexedBasicTree i).associativeWordPolynomial R (standardWord i) = -1
  later :
    ∀ i j, rank i < rank j →
      (indexedBasicTree j).associativeWordPolynomial R (standardWord i) = 0

/-- A diagonal pivot packet is, in particular, a triangular packet. -/
noncomputable def SSPivots.signed_triangular_standardwords
    (R : Type*) [CommRing R]
    {r : ℕ}
    (P : SSPivots (α := α) R r) :
    STWords (α := α) R r where
  standardWord := P.standardWord
  rank i := i
  rank_injective := Fin.val_injective
  diagonal := P.diagonal
  later i j hij :=
    P.offDiagonal i j fun h => by
      subst j
      exact (Nat.lt_irrefl _ hij)

/--
A signed triangular leading-word certificate gives linear independence of the
indexed Hall polynomials in its fixed homogeneous degree.
-/
theorem STWords.word_poly_linindep
    (R : Type*) [CommRing R]
    {r : ℕ}
    (P : STWords (α := α) R r) :
    LinearIndependent R fun i : BasicIndex (α := α) r =>
      (indexedBasicTree i).associativeRepWeight R
        (indexed_tree_weight i) := by
  apply LinearIndependent.of_comp
    (Finsupp.supported R R {word : FreeMonoid α | word.length = r}).subtype
  exact
    finsupp_triangular_pivot R
      (fun i : BasicIndex (α := α) r =>
        (indexedBasicTree i).associativeWordPolynomial R)
      P.standardWord P.rank P.rank_injective P.diagonal P.later

/--
A signed triangular leading-word certificate transfers through the Magnus map
to linear independence in the corresponding free-group lower-central layer.
-/
theorem STWords.freegr_lowec_weigh
    {r : ℕ}
    (P : STWords (α := α) ℤ r)
    (hr : 0 < r) :
    LinearIndependent ℤ fun i : BasicIndex (α := α) r =>
      (indexedBasicTree i).freeLowerWeight
        (indexed_tree_weight i) :=
  free_independent_associative
    hr
    (indexedBasicTree (α := α) (r := r))
    indexed_tree_weight
    (P.word_poly_linindep ℤ)

/--
All-weight signed leading-word triangularity, packaged weight by weight.
-/
structure TriangularStandardSystem
    (R : Type*) [CommRing R] where
  words : ∀ r, STWords (α := α) R r

/-- Completely diagonal all-weight pivots supply triangularity. -/
noncomputable def SSSystem.signed_triangustandar_wordsystem
    (R : Type*) [CommRing R]
    (P : SSSystem (α := α) R) :
    TriangularStandardSystem (α := α) R where
  words r := (P.pivots r).signed_triangular_standardwords R

end HallTree
end Submission
