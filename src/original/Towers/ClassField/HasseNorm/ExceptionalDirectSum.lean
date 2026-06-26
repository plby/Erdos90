import Towers.ClassField.HasseNorm.FiniteStageAssembly
import Mathlib.Data.Finset.Preimage

/-!
# Exceptional finite-place families and the global direct sum

At a finite idèle stage `S`, the nontrivial finite-place degree-two
cohomology is indexed by the finite primes whose associated number-field
places belong to `S`.  This file embeds that finite dependent product into
the direct sum over all finite base primes by extending it by zero.

Enlarging `S` and then extending by zero gives the same direct-sum element.
The supported embeddings are injective, and every element of the global
direct sum belongs to one of their images.  These are exactly the algebraic
facts needed to pass the finite-stage decomposition through the directed
limit in Proposition VII.2.5(b).
-/

namespace Towers.CField.HNorm

open IsDedekindDomain NumberField
open Towers.CField.Ideles
open Towers.CField.ICohomo
open groupCohomology

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance finiteExceptionalNumberFieldPlaceDecidableEq :
    DecidableEq (NumberFieldPlace K) :=
  Classical.decEq _

local instance finiteBasePrimeDecidableEq :
    DecidableEq (HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
  Classical.decEq _

/-- The finite base primes occurring in a finite set of number-field
places.  Infinite places in the set are discarded. -/
noncomputable def exceptionalBasePrimes
    (S : Finset (NumberFieldPlace K)) :
    Finset (HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
  S.preimage Sum.inl Sum.inl_injective.injOn

omit [NumberField K] in
@[simp]
theorem exceptional_base_primes
    (S : Finset (NumberFieldPlace K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    P ∈ exceptionalBasePrimes (K := K) S ↔
      (Sum.inl P : NumberFieldPlace K) ∈ S :=
  Finset.mem_preimage

/-- The unrestricted finite completion-orbit `H²` group at a finite base
prime. -/
abbrev OrbitH2
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) : Type u :=
  H2 (resizedAboveRepresentation
    (K := K) (L := L) P)

/-- The family of unrestricted finite completion-orbit cohomology groups
at the finite primes selected by the stage `S`. -/
abbrev ExceptionalH2
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (NumberFieldPlace K)) :=
  ∀ P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
      (Sum.inl P : NumberFieldPlace K) ∈ S},
    OrbitH2 K L P.1

/-- Reindex the exceptional family by the literal finite preimage of `S`.
This is the indexing form expected by `DirectSum.mk`. -/
noncomputable def exceptionalBaseFamily
    (S : Finset (NumberFieldPlace K)) :
    ExceptionalH2 K L S ≃+
      (∀ P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
          P ∈ exceptionalBasePrimes (K := K) S},
        OrbitH2 K L P.1) where
  toFun x P := x ⟨P.1,
    (exceptional_base_primes (K := K) S P.1).mp P.2⟩
  invFun x P := x ⟨P.1,
    (exceptional_base_primes (K := K) S P.1).mpr P.2⟩
  left_inv x := by
    funext P
    rfl
  right_inv x := by
    funext P
    rfl
  map_add' _ _ := rfl

/-- Extend an exceptional finite-place family by zero to the direct sum over
all finite base primes. -/
noncomputable def resizedExceptionalSum
    (S : Finset (NumberFieldPlace K)) :
    ExceptionalH2 K L S →+
      DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
        (OrbitH2 K L) :=
  (DirectSum.mk (OrbitH2 K L)
    (exceptionalBasePrimes (K := K) S)).comp
      (exceptionalBaseFamily
        (K := K) (L := L) S).toAddMonoidHom

@[simp]
theorem resized_exceptional_sum
    (S : Finset (NumberFieldPlace K))
    (x : ExceptionalH2 K L S)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∈ S) :
    resizedExceptionalSum (K := K) (L := L) S x P =
      x ⟨P, hP⟩ := by
  change DirectSum.mk (OrbitH2 K L)
      (exceptionalBasePrimes (K := K) S)
      (exceptionalBaseFamily
        (K := K) (L := L) S x) P = x ⟨P, hP⟩
  rw [DirectSum.mk_apply_of_mem
    ((exceptional_base_primes (K := K) S P).mpr hP)]
  rfl

@[simp]
theorem resized_exceptional_not
    (S : Finset (NumberFieldPlace K))
    (x : ExceptionalH2 K L S)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hP : (Sum.inl P : NumberFieldPlace K) ∉ S) :
    resizedExceptionalSum (K := K) (L := L) S x P = 0 := by
  change DirectSum.mk (OrbitH2 K L)
      (exceptionalBasePrimes (K := K) S)
      (exceptionalBaseFamily
        (K := K) (L := L) S x) P = 0
  rw [DirectSum.mk_apply_of_notMem]
  exact fun h => hP ((exceptional_base_primes (K := K) S P).mp h)

/-- Enlarge the exceptional family by assigning zero to every newly added
finite prime. -/
noncomputable def resizedExceptionalH
    {S T : Finset (NumberFieldPlace K)} (_hST : S ⊆ T) :
    ExceptionalH2 K L S →+ ExceptionalH2 K L T where
  toFun x P := if hP : (Sum.inl P.1 : NumberFieldPlace K) ∈ S then
    x ⟨P.1, hP⟩
  else
    0
  map_zero' := by
    funext P
    split <;> rfl
  map_add' x y := by
    funext P
    by_cases hP : (Sum.inl P.1 : NumberFieldPlace K) ∈ S
    · simp only [hP, ↓reduceDIte, Pi.add_apply]
    · simp only [hP, ↓reduceDIte, Pi.add_apply, add_zero]

@[simp]
theorem exceptional_h_transition
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (x : ExceptionalH2 K L S)
    (P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
      (Sum.inl P : NumberFieldPlace K) ∈ T})
    (hP : (Sum.inl P.1 : NumberFieldPlace K) ∈ S) :
    resizedExceptionalH (K := K) (L := L) hST x P =
      x ⟨P.1, hP⟩ := by
  simp [resizedExceptionalH, hP]

@[simp]
theorem resized_exceptional_h
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (x : ExceptionalH2 K L S)
    (P : {P : HeightOneSpectrum (NumberField.RingOfIntegers K) //
      (Sum.inl P : NumberFieldPlace K) ∈ T})
    (hP : (Sum.inl P.1 : NumberFieldPlace K) ∉ S) :
    resizedExceptionalH (K := K) (L := L) hST x P = 0 := by
  simp [resizedExceptionalH, hP]

/-- Extending an exceptional family by zero is compatible with embedding it
in the fixed global direct sum. -/
theorem exceptional_h_direct
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T)
    (x : ExceptionalH2 K L S) :
    resizedExceptionalSum (K := K) (L := L) T
        (resizedExceptionalH
          (K := K) (L := L) hST x) =
      resizedExceptionalSum (K := K) (L := L) S x := by
  apply DirectSum.ext
  intro P
  by_cases hPS : (Sum.inl P : NumberFieldPlace K) ∈ S
  · have hPT : (Sum.inl P : NumberFieldPlace K) ∈ T := hST hPS
    rw [resized_exceptional_sum
      (K := K) (L := L) T _ P hPT,
      exceptional_h_transition
        (K := K) (L := L) hST _ ⟨P, hPT⟩ hPS,
      resized_exceptional_sum
        (K := K) (L := L) S x P hPS]
  · rw [resized_exceptional_not
      (K := K) (L := L) S x P hPS]
    by_cases hPT : (Sum.inl P : NumberFieldPlace K) ∈ T
    · rw [resized_exceptional_sum
        (K := K) (L := L) T _ P hPT,
        resized_exceptional_h
          (K := K) (L := L) hST _ ⟨P, hPT⟩ hPS]
    · rw [resized_exceptional_not
        (K := K) (L := L) T _ P hPT]

/-- The supported embedding at every finite stage is injective. -/
theorem resized_direct_injective
    (S : Finset (NumberFieldPlace K)) :
    Function.Injective
      (resizedExceptionalSum (K := K) (L := L) S) :=
  (DirectSum.mk_injective
    (exceptionalBasePrimes (K := K) S)).comp
      (exceptionalBaseFamily
        (K := K) (L := L) S).injective

/-- Every element of the finite-prime direct sum is represented by an
exceptional family at some finite set of number-field places. -/
theorem exceptional_h_preimage
    (y : DirectSum (HeightOneSpectrum (NumberField.RingOfIntegers K))
      (OrbitH2 K L)) :
    ∃ (S : Finset (NumberFieldPlace K)) (x : ExceptionalH2 K L S),
      resizedExceptionalSum (K := K) (L := L) S x = y := by
  classical
  let S : Finset (NumberFieldPlace K) :=
    y.support.image (fun P => (Sum.inl P : NumberFieldPlace K))
  have hmem (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
      (Sum.inl P : NumberFieldPlace K) ∈ S ↔ P ∈ y.support := by
    simp only [S, Finset.mem_image]
    constructor
    · rintro ⟨Q, hQ, hQP⟩
      exact Sum.inl_injective hQP |>.symm ▸ hQ
    · exact fun hP => ⟨P, hP, rfl⟩
  let x : ExceptionalH2 K L S := fun P => y P.1
  refine ⟨S, x, ?_⟩
  apply DirectSum.ext
  intro P
  by_cases hP : P ∈ y.support
  · rw [resized_exceptional_sum
      (K := K) (L := L) S x P ((hmem P).mpr hP)]
  · rw [resized_exceptional_not
      (K := K) (L := L) S x P (fun h => hP ((hmem P).mp h))]
    exact (DFinsupp.notMem_support_iff.mp hP).symm

end

end Towers.CField.HNorm
