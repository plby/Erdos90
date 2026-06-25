import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Submission.ClassField.Ramification.FilteredGroupRigidity

/-!
# Class Field Theory, Chapter I, Lemma 4.10: descent to a finite stage

Milne first observes that the finitely many coefficients of a minimal
polynomial over `K_π` already lie in one finite layer `K_{π,n}`.  The theorem
below is the exact directed-union argument, stated for any monotone tower of
intermediate fields.
-/

namespace Submission.CField.Ramification

/-- A finite subset of a monotone union of intermediate fields is contained
in a single stage. -/
theorem i_sup_intermediate
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K : ℕ → IntermediateField F E) (hK : Monotone K)
    {s : Set E} (hs : s.Finite)
    (hsub : s ⊆ (⨆ n, K n : IntermediateField F E)) :
    ∃ n, s ⊆ K n := by
  classical
  have hstage : ∀ x ∈ s, ∃ n, x ∈ K n := by
    intro x hx
    have hxSup : x ∈ ⨆ n, K n := hsub hx
    rw [← SetLike.mem_coe,
      IntermediateField.coe_iSup_of_directed hK.directed_le,
      Set.mem_iUnion] at hxSup
    exact hxSup
  choose stage hstage using hstage
  let stage' : E → ℕ := fun x => if hx : x ∈ s then stage x hx else 0
  have hstage' : ∀ x ∈ s, x ∈ K (stage' x) := by
    intro x hx
    simpa [stage', hx] using hstage x hx
  refine ⟨hs.toFinset.sup stage', ?_⟩
  intro x hx
  exact hK (Finset.le_sup (hs.mem_toFinset.mpr hx)) (hstage' x hx)

end Submission.CField.Ramification
