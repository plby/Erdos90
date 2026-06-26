import Submission.ClassField.NormLimitation.OpenCore
import Submission.ClassField.NormLimitation.KummerNorm
import Submission.ClassField.NormLimitation.ExponentGroupAssembly

/-! # Chapter VII, Section 9, Lemma 9.3 -/

namespace Submission.CField.NLimita

open Submission.CField.Recip

noncomputable section

universe u

/-- **Lemma VII.9.3.**  The exponent-`p` case of the existence theorem,
assembled from the actual open-neighborhood and `S`-unit Kummer field
constructions. -/
theorem exponent_global_reciprocity
    (hArtin : ∀ (K : Type u) [Field K] [NumberField K],
      GlobalArtinProposition (K := K))
    (hrec : ∀ (K : Type u) [Field K] [NumberField K],
      IdeleReciprocityLaw (K := K)) :
    ExistenceStatementInterface.{u} :=
  exponent_prime_bridges
    (global_reciprocity_statement hArtin hrec)
    openCoreBridge
    (kummer_core_reciprocity hArtin hrec)

end

end Submission.CField.NLimita
