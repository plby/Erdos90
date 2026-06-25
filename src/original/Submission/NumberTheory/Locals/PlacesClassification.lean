import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic


/-!
# The places of a number field

This file records the three classification clauses in Milne's Theorem 7.14
using Mathlib's types of finite and infinite places.  Finite places are
equivalent to height-one prime ideals.  Real infinite places are equivalent to
real complex embeddings.  Nonreal complex embeddings map surjectively to
complex infinite places, with fibers consisting exactly of a conjugate pair.

Mathlib's `FinitePlace` and `InfinitePlace` are already the classified place
types.  This file does not assert, separately, that every arbitrary nontrivial
absolute value on a number field belongs to one of them.
-/

namespace Submission.NumberTheory.Milne

open IsDedekindDomain NumberField

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- Milne, Theorem 7.14(a): finite places are in bijection with the nonzero
prime ideals of the ring of integers.  For a Dedekind domain these are encoded
by `HeightOneSpectrum`. -/
def placesPrimeIdeals :
    FinitePlace K ≃ HeightOneSpectrum (𝓞 K) :=
  FinitePlace.equivHeightOneSpectrum

/-- The finite place attached to a nonzero prime ideal determines that ideal
uniquely. -/
theorem place_mk_injective :
    Function.Injective (FinitePlace.mk (K := K)) := by
  intro v w h
  exact FinitePlace.mk_eq_iff.mp h

/-- Milne, Theorem 7.14(b): real infinite places are in bijection with complex
embeddings fixed by complex conjugation, the standard Mathlib encoding of real
embeddings. -/
def realEmbeddingsPlaces :
    {φ : K →+* ℂ // NumberField.ComplexEmbedding.IsReal φ} ≃
      {w : InfinitePlace K // InfinitePlace.IsReal w} :=
  InfinitePlace.mkReal

omit [NumberField K] in
/-- Milne, Theorem 7.14(c), uniqueness clause: two complex embeddings define
the same infinite place exactly when they are equal or complex conjugate. -/
theorem complex_embeddings_same
    (φ ψ : {φ : K →+* ℂ // ¬NumberField.ComplexEmbedding.IsReal φ}) :
    InfinitePlace.mkComplex φ = InfinitePlace.mkComplex ψ ↔
      (φ : K →+* ℂ) = ψ ∨
        NumberField.ComplexEmbedding.conjugate (φ : K →+* ℂ) = ψ := by
  rw [Subtype.ext_iff, InfinitePlace.mkComplex_coe,
    InfinitePlace.mkComplex_coe, InfinitePlace.mk_eq_iff]

omit [NumberField K] in
/-- Milne, Theorem 7.14(c), existence clause: every complex infinite place is
represented by a nonreal complex embedding. -/
theorem complex_embeddings_surjective :
    Function.Surjective
      (InfinitePlace.mkComplex (K := K) :
        {φ : K →+* ℂ // ¬NumberField.ComplexEmbedding.IsReal φ} →
          {w : InfinitePlace K // InfinitePlace.IsComplex w}) := by
  intro w
  refine ⟨⟨InfinitePlace.embedding w.1,
    InfinitePlace.isComplex_iff.mp w.2⟩, ?_⟩
  apply Subtype.ext
  exact InfinitePlace.mk_embedding w.1

/-- Every infinite place is uniquely tagged as real or complex. -/
def realOrComplex :
    InfinitePlace K ≃
      {w : InfinitePlace K // InfinitePlace.IsReal w} ⊕
        {w : InfinitePlace K // InfinitePlace.IsComplex w} := by
  classical
  let e : InfinitePlace K ≃
      {w : InfinitePlace K //
        InfinitePlace.IsReal w ∨ InfinitePlace.IsComplex w} := {
    toFun w := ⟨w, InfinitePlace.isReal_or_isComplex w⟩
    invFun w := w.1
    left_inv _ := rfl
    right_inv _ := rfl
  }
  exact e.trans <|
    subtypeOrEquiv InfinitePlace.IsReal InfinitePlace.IsComplex
      (InfinitePlace.disjoint_isReal_isComplex K)

/-- A single exact packaging of the finite/real/complex trichotomy in
Theorem 7.14. -/
def classifiedPlacesEquiv :
    (FinitePlace K ⊕ InfinitePlace K) ≃
      HeightOneSpectrum (𝓞 K) ⊕
        ({w : InfinitePlace K // InfinitePlace.IsReal w} ⊕
          {w : InfinitePlace K // InfinitePlace.IsComplex w}) :=
  Equiv.sumCongr (placesPrimeIdeals K)
    (realOrComplex K)

end

end Submission.NumberTheory.Milne
