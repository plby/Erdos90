import Submission.ClassField.NormLimitation.ExistenceStatement

/-!
# Chapter VII, Section 9, Lemma 9.3: statement

The literal exponent-`p` existence statement is kept separate from its
topological and Kummer-theoretic proof interfaces.  Later group-theoretic
reductions therefore depend only on the theorem they use.
-/

namespace Submission.CField.NLimita

open NumberField
open Submission.CField.Ideles
open Submission.CField.Recip

noncomputable section

universe u

private abbrev CK (K : Type u) [Field K] [NumberField K] :=
  IdeleClassGroup (RingOfIntegers K) K

/-- **Lemma VII.9.3 (source statement).** -/
def ExistenceStatementInterface : Prop :=
  ∀ (p : ℕ) (K : Type u) [Field K] [NumberField K],
    p.Prime → (primitiveRoots p K).Nonempty →
    ∀ V : Subgroup (CK K),
      IsOpen (V : Set (CK K)) → V.FiniteIndex →
      (∀ q : CK K ⧸ V, q ^ p = 1) →
      IdeleNormGroup K V

end

end Submission.CField.NLimita
