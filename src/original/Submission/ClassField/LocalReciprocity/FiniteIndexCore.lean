import Mathlib.GroupTheory.Index

/-!
# Milne, Class Field Theory, Theorem III.3.5: finite-index core

In the Galois case of the Norm Limitation Theorem, norm transitivity gives an
inclusion of norm subgroups and local reciprocity shows that both subgroups
have the same finite index.  The following group-theoretic lemma is the final
step of that argument.
-/

namespace Submission.CField.LRecip

universe u

variable {G : Type u} [Group G]

/-- A finite-index subgroup cannot be properly contained in another subgroup
of the same index. -/
theorem subgroup_index
    {H K : Subgroup G} [H.FiniteIndex]
    (hHK : H ≤ K) (hindex : H.index = K.index) : H = K := by
  apply le_antisymm hHK
  by_contra hKH
  have hne : H ≠ K := by
    intro hEq
    apply hKH
    rw [hEq]
  have hstrict : H < K := lt_of_le_of_ne hHK hne
  have hlt : K.index < H.index := Subgroup.index_strictAnti hstrict
  omega

/-- The Galois-case conclusion of norm limitation, abstracted to its two
inputs: norm-subgroup containment and equality of indices. -/
theorem subgroups_equal_containment
    (NL NE : Subgroup G) [NL.FiniteIndex]
    (hcontain : NL ≤ NE) (hindex : NL.index = NE.index) : NL = NE :=
  subgroup_index hcontain hindex

end Submission.CField.LRecip
