import Mathlib.GroupTheory.Complement
import Mathlib.RepresentationTheory.Invariants

/-!
# Milne, Class Field Theory, Example II.1.29 in degree zero

Let `H` be a finite-index subgroup of `G`, let `S` be a left transversal, and let `m` be an
`H`-invariant vector in a `G`-representation.  Milne defines the degree-zero corestriction by

`m \mapsto \sum_{s \in S} s m`.

We index the sum by the finite left-coset space `G ⧸ H`, using the representative supplied by
`S`.  The resulting sum is independent of the transversal and is fixed by `G`.
-/

namespace Submission.CField.COps

open scoped BigOperators

universe u

variable {k G : Type u} [CommRing k] [Group G]

section

variable (A : Rep k G) (H : Subgroup G) [H.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The sum over a left transversal used to define corestriction in degree zero. -/
noncomputable def transversalNorm (S : H.LeftTransversal) (m : A) : A :=
  ∑ q : G ⧸ H, A.ρ (S.2.leftQuotientEquiv q : G) m

omit [H.FiniteIndex] in
lemma representative_smul_invariants
    (m : A) (hm : m ∈ Representation.invariants (A.ρ.comp H.subtype))
    (S T : H.LeftTransversal) (q : G ⧸ H) :
    A.ρ (S.2.leftQuotientEquiv q : G) m =
      A.ρ (T.2.leftQuotientEquiv q : G) m := by
  let s : G := S.2.leftQuotientEquiv q
  let t : G := T.2.leftQuotientEquiv q
  have hst : s⁻¹ * t ∈ H := by
    apply QuotientGroup.leftRel_apply.mp
    apply Quotient.exact'
    simpa [s, t] using
      (S.2.quotientGroupMk_leftQuotientEquiv q).trans
        (T.2.quotientGroupMk_leftQuotientEquiv q).symm
  let h : H := ⟨s⁻¹ * t, hst⟩
  have ht : t = s * h := by
    simp [h]
  calc
    A.ρ s m = A.ρ s (A.ρ h m) := by
      congr 1
      simpa using (hm h).symm
    _ = A.ρ (s * h) m := by simp [map_mul]
    _ = A.ρ t m := by rw [ht]

/-- The degree-zero transversal norm does not depend on the chosen left transversal. -/
theorem transversalNorm_eq
    (m : A) (hm : m ∈ Representation.invariants (A.ρ.comp H.subtype))
    (S T : H.LeftTransversal) :
    transversalNorm A H S m = transversalNorm A H T m := by
  simp only [transversalNorm]
  apply Fintype.sum_congr
  intro q
  exact representative_smul_invariants A H m hm S T q

/-- The degree-zero transversal norm is fixed by the whole group. -/
theorem transversal_norm_invariants
    (m : A) (hm : m ∈ Representation.invariants (A.ρ.comp H.subtype))
    (S : H.LeftTransversal) :
    transversalNorm A H S m ∈ A.ρ.invariants := by
  rw [Representation.mem_invariants]
  intro g
  calc
    A.ρ g (transversalNorm A H S m) =
        ∑ q : G ⧸ H, A.ρ g (A.ρ (S.2.leftQuotientEquiv q : G) m) := by
          simp [transversalNorm]
    _ = ∑ q : G ⧸ H, A.ρ (g * (S.2.leftQuotientEquiv q : G)) m := by
          apply Fintype.sum_congr
          intro q
          simp [map_mul]
    _ = ∑ q : G ⧸ H,
        A.ρ ((g • S).2.leftQuotientEquiv (g • q) : G) m := by
          apply Fintype.sum_congr
          intro q
          rw [← Subgroup.smul_leftQuotientEquiv (H := H) g S q]
          rfl
    _ = transversalNorm A H (g • S) m := by
          exact Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun _ ↦ rfl)
    _ = transversalNorm A H S m := transversalNorm_eq A H m hm _ _

/-- Degree-zero corestriction, as a linear map from `H`-invariants to `G`-invariants. -/
noncomputable def corestrictionZero (S : H.LeftTransversal) :
    Representation.invariants (A.ρ.comp H.subtype) →ₗ[k] A.ρ.invariants :=
  { toFun := fun m ↦ ⟨transversalNorm A H S m, transversal_norm_invariants A H m m.2 S⟩
    map_add' := by
      intro x y
      ext
      simp [transversalNorm, Finset.sum_add_distrib]
    map_smul' := by
      intro r x
      ext
      simp [transversalNorm, Finset.smul_sum] }

/-- Degree-zero corestriction is independent of the transversal. -/
theorem corestrictionZero_eq (S T : H.LeftTransversal) :
    corestrictionZero A H S = corestrictionZero A H T := by
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  exact transversalNorm_eq A H m m.2 S T

end

end Submission.CField.COps
