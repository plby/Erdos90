import Submission.ClassField.BrauerGroups.RelativeBrauerGroup

/-!
# Milne, Class Field Theory, Proposition IV.2.17: source statement

The tracked `finite_splitting_field` theorem proves the representative-
level content of Proposition IV.2.17.  This file passes to arbitrary Brauer
classes and records Milne's literal union over the finite subextensions of the
fixed algebraic closure `AlgebraicClosure k`.
-/

namespace Submission.CField.BGroups

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- Every Brauer class belongs to the relative Brauer group of some finite
subextension of the fixed algebraic closure. -/
theorem subextension_relative_brauer
    (x : BrauerGroup.{u, u} k) :
    ∃ (K : IntermediateField k (AlgebraicClosure k))
      (_ : FiniteDimensional k K),
      x ∈ relativeBrauerGroup k K := by
  induction x using Quotient.inductionOn with
  | _ A =>
      obtain ⟨K, hKfinite, hsplit⟩ := finite_splitting_field k A
      letI : FiniteDimensional k K := hKfinite
      refine ⟨K, inferInstance, ?_⟩
      exact
        (brauer_relative_split k K A).2 hsplit

/-- **Proposition IV.2.17 (literal union statement).**

`Br(k)` is the union of `Br(K/k)` as `K` ranges over the finite extensions
of `k` contained in the fixed algebraic closure. -/
theorem i_union_relative :
    (Set.univ : Set (BrauerGroup.{u, u} k)) =
      ⋃ (K : IntermediateField k (AlgebraicClosure k))
        (_ : FiniteDimensional k K),
        (relativeBrauerGroup k K : Set (BrauerGroup.{u, u} k)) := by
  symm
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨K, hKfinite, hx⟩ :=
    subextension_relative_brauer k x
  exact Set.mem_iUnion_of_mem K (Set.mem_iUnion_of_mem hKfinite hx)

end

end Submission.CField.BGroups
