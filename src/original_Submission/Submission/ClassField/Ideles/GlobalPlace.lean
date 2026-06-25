import Submission.ClassField.Ideles.FinitePlaceCompletion

/-!
# Places and completions of a number field

This file supplies the common place index needed by the local-to-global
statements in Chapters VII and VIII.  Finite places use the adic completions
appearing in the finite ideles; infinite places use Mathlib's absolute-value
completions.
-/

namespace Submission.CField.Ideles

open AbsoluteValue UniformSpace
open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne

noncomputable section

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The finite and infinite places of a number field. -/
abbrev NumberFieldPlace :=
  HeightOneSpectrum (NumberField.RingOfIntegers K) ⊕ InfinitePlace K

/-- The completion of a number field at a finite or infinite place. -/
def placeCompletion : NumberFieldPlace K → Type u
  | .inl v => v.adicCompletion K
  | .inr v => v.Completion

instance (v : NumberFieldPlace K) : Field (placeCompletion K v) := by
  cases v <;> simp only [placeCompletion] <;> infer_instance

instance (v : NumberFieldPlace K) : TopologicalSpace (placeCompletion K v) := by
  cases v <;> simp only [placeCompletion] <;> infer_instance

/-- Every place completion carries its canonical `K`-algebra structure. -/
instance (v : NumberFieldPlace K) : Algebra K (placeCompletion K v) := by
  cases v with
  | inl v =>
      simp only [placeCompletion]
      exact (FinitePlace.embedding v).toAlgebra
  | inr v =>
      simp only [placeCompletion]
      exact (completionEmbedding v.1).toAlgebra

/-- The canonical embedding into a place completion. -/
def placeEmbedding (v : NumberFieldPlace K) : K →+* placeCompletion K v := by
  cases v with
  | inl v => exact algebraMap K (v.adicCompletion K)
  | inr v => exact completionEmbedding v.1

end

end Submission.CField.Ideles
