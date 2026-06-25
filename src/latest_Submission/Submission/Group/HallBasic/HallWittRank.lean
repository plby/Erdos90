import Submission.Group.HallBasic.Weight
import Mathlib.Data.Sym.Card


/-!
# Cardinalities of Hall basic commutators

This file computes the first nontrivial Hall number used in the examples
following Corollary 9.3.  Weight-two basic commutators are canonically the
unordered pairs of distinct generators.
-/

noncomputable section

namespace Submission
namespace HallTree

variable {α : Type} [Fintype α] [DecidableEq α] [Encodable α]

@[reducible] private noncomputable def atomLinearOrder : LinearOrder α :=
  LinearOrder.lift' atom (by
    intro a b h
    injection h)

local instance : LinearOrder α := atomLinearOrder

private def increasingGeneratorPairs :=
  {p : α × α // p.1 < p.2}

private def increasingPairTree
    (p : increasingGeneratorPairs (α := α)) :
    {w : HallTree α // w.IsBasic ∧ w.weight = 2} :=
  ⟨commutator (atom p.1.2) (atom p.1.1),
    basic_commutator_admissible
      (isBasic_atom _) (isBasic_atom _) p.2 trivial,
    by simp⟩

omit [Fintype α] [DecidableEq α] in
private theorem increasing_tree_bijective :
    Function.Bijective
      (increasingPairTree (α := α)) := by
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · exact HallTree.atom.inj
        (HallTree.commutator.inj
          (Subtype.ext_iff.mp hpq)).2
    · exact HallTree.atom.inj
        (HallTree.commutator.inj
          (Subtype.ext_iff.mp hpq)).1
  · rintro ⟨w, hwbasic, hwweight⟩
    obtain ⟨a, b, rfl⟩ :=
      commutator_atoms_two hwweight
    have hba : b < a := by
      change atom b < atom a
      exact (isBasic_commutator _ _).mp hwbasic |>.2.2.1
    exact ⟨⟨(b, a), hba⟩, rfl⟩

private noncomputable def increasingPairsTrees :
    increasingGeneratorPairs (α := α) ≃
      {w : HallTree α // w.IsBasic ∧ w.weight = 2} :=
  Equiv.ofBijective increasingPairTree
    increasing_tree_bijective

private def increasingDistinctSym
    (p : increasingGeneratorPairs (α := α)) :
    {z : Sym2 α // ¬z.IsDiag} :=
  ⟨s(p.1.1, p.1.2), by
    simpa using ne_of_lt p.2⟩

omit [Fintype α] [DecidableEq α] in
private theorem increasing_distinct_sym :
    Function.Bijective (increasingDistinctSym (α := α)) := by
  constructor
  · intro p q hpq
    have hsym :
        s(p.1.1, p.1.2) = s(q.1.1, q.1.2) :=
      Subtype.ext_iff.mp hpq
    rcases Sym2.eq_iff.mp hsym with h | h
    · exact Subtype.ext (Prod.ext h.1 h.2)
    · exfalso
      have hp := p.2
      have hq := q.2
      rw [h.1, h.2] at hp
      exact asymm hp hq
  · rintro ⟨z, hz⟩
    induction z using Sym2.inductionOn with
    | _ a b =>
        have hab : a ≠ b := by
          simpa using hz
        rcases lt_or_gt_of_ne hab with hab | hba
        · exact ⟨⟨(a, b), hab⟩, rfl⟩
        · refine ⟨⟨(b, a), hba⟩, ?_⟩
          apply Subtype.ext
          exact Sym2.eq_swap

private noncomputable def increasingPairsSym :
    increasingGeneratorPairs (α := α) ≃
      {z : Sym2 α // ¬z.IsDiag} :=
  Equiv.ofBijective increasingDistinctSym
    increasing_distinct_sym

/-- Weight-two Hall indices are canonically unordered pairs of distinct
generators. -/
noncomputable def distinctSym2 :
    BasicIndex (α := α) 2 ≃ {z : Sym2 α // ¬z.IsDiag} :=
  (basicIndexEquiv (α := α) 2).trans
    increasingPairsTrees.symm |>.trans
      increasingPairsSym

/-- The number of weight-two basic Hall commutators is `choose |α| 2`. -/
theorem card_basic_index :
    Fintype.card (BasicIndex (α := α) 2) =
      (Fintype.card α).choose 2 := by
  rw [Fintype.card_congr
    (distinctSym2 (α := α))]
  exact Sym2.card_subtype_not_diag

end HallTree
end Submission
