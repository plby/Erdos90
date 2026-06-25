import Submission.ClassField.CrossedProducts.Classification
import Submission.ClassField.CrossedProducts.CohomologyClass
import Submission.ClassField.CrossedProducts.CohomologousProducts
import Submission.ClassField.CrossedProducts.CrossedProductBrauer
import Submission.ClassField.CrossedProducts.Injectivity

/-!
# Chapter IV, Theorem 3.11: statement

This bundles Milne's class `A(L/k)` so that the surjectivity and fiber
assertions for the factor-set map can be stated literally.
-/

namespace Submission.CField.CProduca

noncomputable section

universe u

attribute [local instance] Units.mulDistribMulActionRight

/-- A member of Milne's `A(L/k)`: a central simple `k`-algebra containing
`L`, whose dimension over `k` is `[L:k]^2`. -/
structure MSAlg
    (k L : Type u) [Field k] [Field L] [Algebra k L] where
  carrier : Type u
  [ring : Ring carrier]
  [nontrivial : Nontrivial carrier]
  [algebra : Algebra k carrier]
  [simple : IsSimpleRing carrier]
  [central : Algebra.IsCentral k carrier]
  [finite : Module.Finite k carrier]
  embedding : L →ₐ[k] carrier
  finrank_sq : Module.finrank k carrier = (Module.finrank k L) ^ 2

attribute [instance] MSAlg.ring
  MSAlg.nontrivial
  MSAlg.algebra
  MSAlg.simple
  MSAlg.central
  MSAlg.finite

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]

/-- The cohomology class of the normalized factor set attached to a member
of `A(L/k)`. -/
def galoisSetClass (A : MSAlg k L) :
    MHTwo Gal(L/k) Lˣ :=
  MHTwo.mk
    (galoisNormalizedCocycle k L A.carrier A.embedding A.finrank_sq)

/-- The isomorphism relation occurring as the fibers of `gamma`. -/
def MSAlg.IsIsomorphic
    (A B : MSAlg k L) : Prop :=
  Nonempty (A.carrier ≃ₐ[k] B.carrier)

/-- **Theorem IV.3.11, statement.** The factor-set map from `A(L/k)` to
`H^2(L/k)` is surjective, and its fibers are precisely the `k`-algebra
isomorphism classes. -/
def GaloisSetClassification : Prop :=
  Function.Surjective (galoisSetClass k L) ∧
    ∀ A B, galoisSetClass k L A = galoisSetClass k L B ↔
      MSAlg.IsIsomorphic (k := k) (L := L) A B

/-- **Theorem IV.3.11.** The bundled factor-set classification holds. -/
theorem galoisSetClassification :
    GaloisSetClassification k L := by
  constructor
  · intro x
    obtain ⟨c, rfl⟩ := MHTwo.exists_mk_eq x
    let A : MSAlg k L :=
      { carrier := CProduc c
        embedding := CProduc.fieldEmbedding k L c
        finrank_sq := CProduc.finrank_over_base k L c }
    refine ⟨A, ?_⟩
    apply (MHTwo.mk_eq_iff _ _).2
    apply MHTwo.isCohomologous_symm
    exact CProduc.cohomologous_alg_equiv k L c
      (galoisNormalizedCocycle k L A.carrier A.embedding A.finrank_sq)
      (algCrossedEmbedding k L A.carrier A.embedding A.finrank_sq)
  · intro A B
    let cA := galoisNormalizedCocycle k L A.carrier A.embedding A.finrank_sq
    let cB := galoisNormalizedCocycle k L B.carrier B.embedding B.finrank_sq
    let eA : A.carrier ≃ₐ[k] CProduc cA :=
      algCrossedEmbedding k L A.carrier A.embedding A.finrank_sq
    let eB : B.carrier ≃ₐ[k] CProduc cB :=
      algCrossedEmbedding k L B.carrier B.embedding B.finrank_sq
    constructor
    · intro h
      have hcoh : MHTwo.IsCohomologous cA cB :=
        (MHTwo.mk_eq_iff cA cB).1 h
      exact ⟨eA.trans
        ((CProduc.algMulCoboundary₂ k L cA cB hcoh).trans eB.symm)⟩
    · rintro ⟨e⟩
      apply (MHTwo.mk_eq_iff cA cB).2
      exact CProduc.cohomologous_alg_equiv k L cA cB
        (eA.symm.trans (e.trans eB))

end

end Submission.CField.CProduca
