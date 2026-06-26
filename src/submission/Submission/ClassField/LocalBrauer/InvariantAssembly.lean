import Submission.ClassField.LocalBrauer.BrauerCofinalLimit
import Submission.ClassField.LocalBrauer.InvariantLimitAssembly

/-!
# Chapter IV, Section 4: assembling the Brauer invariant

This file composes the two formal direct-limit steps in Proposition IV.4.3.
A cofinal nested sequence of relative Brauer groups has direct limit
`BrauerGroup K`; compatible finite invariants identify the same direct limit
with `Q/Z`.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open BGroups CProduca

variable (K : Type u) [Field K]
variable (L : ℕ → FiniteGaloisIntermediateField K (SeparableClosure K))
variable (hL : Monotone L)

variable (e : ∀ r, brauerCofinalLevel K L r ≃*
  invariantTorsionLevel r)

variable (he : ∀ r s h x,
  e s (brauerCofinalInclusion K L hL r s h x) =
    invariantTorsionInclusion r s h (e r x))

variable (hcofinal : ∀ x : BrauerGroup K,
  ∃ r, x ∈ relativeBrauerGroup K (L r))

/-- **Proposition IV.4.3, formal assembly.** Compatible finite local
invariants on a cofinal nested sequence assemble to an isomorphism from the
absolute Brauer group to `Q/Z`. -/
def localBrauerInvariant :
    BrauerGroup K ≃* Multiplicative LocalInvariant :=
  (brauerCofinalEquiv K L hL hcofinal).symm.trans
    (invariantLimitAssembly
      (brauerCofinalInclusion K L hL) e he)

/-- The assembled invariant restricts to the prescribed finite invariant at
every level. -/
@[simp]
theorem brauer_invariant_coe
    (r : ℕ) (x : brauerCofinalLevel K L r) :
    localBrauerInvariant K L hL e he hcofinal (x : BrauerGroup K) =
      invariantTorsionMul r (e r x) := by
  change invariantLimitAssembly
      (brauerCofinalInclusion K L hL) e he
      ((brauerCofinalEquiv K L hL hcofinal).symm
        (x : BrauerGroup K)) = _
  have hx :
      (brauerCofinalEquiv K L hL hcofinal).symm
          (x : BrauerGroup K) =
        (⟦⟨r, x⟩⟧ : brauerCofinalLimit K L hL) := by
    apply (brauerCofinalEquiv K L hL hcofinal).injective
    simp
  rw [hx]
  exact limit_assembly_mk
    (brauerCofinalInclusion K L hL) e he r x

end

end Submission.CField.LBrauer
