import Submission.ClassField.LocalExistence.IsDivisibleSubgroup

/-!
# Milne, Class Field Theory, Section III.5, Step 4

Milne proves that the intersection `D_K` of all finite-extension norm groups
is trivial by placing it in a family of open finite-index subgroups whose
intersection is trivial.  The final implication is purely lattice-theoretic.
-/

namespace Submission.CField.LExist

universe u v w

variable {Z : Type u} [CommGroup Z]

/-- **Step III.5.4, separating-family core.** If the core of one family of
subgroups lies in every member of a separating family, then it is trivial. -/
theorem core_bot_separating
    {ι : Type v} {κ : Type w} (N : ι → Subgroup Z) (V : κ → Subgroup Z)
    (hle : ∀ k, familyCore N ≤ V k) (hseparates : (⨅ k, V k) = ⊥) :
    familyCore N = ⊥ := by
  apply le_antisymm
  · rw [← hseparates]
    exact le_iInf hle
  · exact bot_le

end Submission.CField.LExist
