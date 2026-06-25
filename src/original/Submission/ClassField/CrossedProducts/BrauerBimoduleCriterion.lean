import Submission.ClassField.BrauerGroups.BrauerGroup

/-!
# A bimodule criterion for Brauer equivalence

Two finite-dimensional central simple algebras are Brauer equivalent when
their tensor product with one factor opposite acts as the full endomorphism
algebra of a finite nonzero vector space.
-/

namespace Submission.CField.CProduca

noncomputable section

open scoped TensorProduct

universe u

/-- If `C tensor D^op` is the full endomorphism algebra of a finite nonzero
`k`-vector space, then `C` and `D` are Brauer equivalent. -/
theorem equivalent_op_end
    (k C D V : Type u) [Field k]
    [Ring C] [Algebra k C] [IsSimpleRing C] [Algebra.IsCentral k C]
    [Module.Finite k C]
    [Ring D] [Algebra k D] [IsSimpleRing D] [Algebra.IsCentral k D]
    [Module.Finite k D]
    [AddCommGroup V] [Module k V] [Module.Finite k V] [Nontrivial V]
    (e : C ⊗[k] Dᵐᵒᵖ ≃ₐ[k] Module.End k V) :
    IsBrauerEquivalent
      (BGroups.centralSimpleCSA k C)
      (BGroups.centralSimpleCSA k D) := by
  let q := Module.finrank k V
  let eMatrix : C ⊗[k] Dᵐᵒᵖ ≃ₐ[k] Matrix (Fin q) (Fin q) k :=
    e.trans (algEquivMatrix (Module.finBasis k V))
  have hq : q ≠ 0 := (Module.finrank_pos (R := k) (M := V)).ne'
  let Cc := BGroups.centralSimpleCSA k C
  let Dc := BGroups.centralSimpleCSA k D
  have hsplit : IsBrauerEquivalent
      (BGroups.tensorCSA k Cc
        (BGroups.oppositeCSA k Dc))
      (BGroups.baseFieldCSA k) :=
    BGroups.brauer_equivalent_matrix
      k _ q hq eMatrix
  have hclass :=
    (BGroups.brauer_class k _ _).2 hsplit
  change BGroups.brauerClass k Cc *
      (BGroups.brauerClass k Dc)⁻¹ = 1 at hclass
  apply (BGroups.brauer_class k _ _).1
  exact mul_inv_eq_one.mp hclass

end

end Submission.CField.CProduca
