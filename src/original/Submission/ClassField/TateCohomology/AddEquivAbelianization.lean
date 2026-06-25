import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree

/-!
# Milne, Class Field Theory, Proposition II.2.7

Mathlib proves the more general formula
`H₁(G, A) ≃ Gᵃᵇ ⊗ℤ A` whenever the action on `A` is trivial.  Specializing
to `A = ℤ` and applying the right-unit isomorphism gives Milne's canonical
identification `H₁(G, ℤ) ≃ Gᵃᵇ`.

Milne's preceding Lemma II.2.6 identifies the abelianization with the quotient
of the augmentation ideal by its square.  Mathlib currently has no packaged
augmentation-ideal API for integral group rings, so this proof uses the
stronger direct computation of first group homology instead.
-/

namespace Submission.CField.TCohomo

/-- **Proposition II.2.7.** First integral group homology is canonically the
additive group underlying the abelianization. -/
noncomputable def homology1Abelianization
    (G : Type) [Group G] :
    groupHomology (Rep.trivial ℤ G ℤ) 1 ≃+ Additive (Abelianization G) :=
  (groupHomology.H1AddEquivOfIsTrivial (Rep.trivial ℤ G ℤ)).trans
    (TensorProduct.rid ℤ (Additive (Abelianization G))).toAddEquiv

end Submission.CField.TCohomo
