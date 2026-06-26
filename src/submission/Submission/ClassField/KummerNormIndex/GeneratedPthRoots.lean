import Submission.ClassField.KummerNormIndex.FinitePrimePart
import Submission.ClassField.KummerNormIndex.PrincipalIdeleHom
import Submission.ClassField.KummerNormIndex.ObviousMap
import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# Chapter VII, Section 6, Lemma 6.9

For the set `T` selected in Lemma 6.2, Milne considers the diagonal map

`U(S) → ∏ P ∈ T, U_P / U_P^p`.

Here `U_P` is literally the unit group of the completed valuation ring
`P.adicCompletionIntegers K`.  The map is constructed below from the
canonical completion embeddings.  Its surjectivity follows formally once
the two numerical calculations in the printed proof are supplied:

* the kernel has index `p ^ T.card`, by Lemma 6.3 and Kummer theory;
* the finite target has cardinality `p ^ T.card`, by Proposition 6.8.

The source statement retains the Kummer extension and the Frobenius-basis
hypothesis producing `T`; it does not claim this surjectivity for an arbitrary
finite set of primes.
-/

namespace Submission.CField.KNIndex

open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.HQuotie

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

/-- The equality `M = K[U(S)^(1/p)]` from the notation preceding Lemma
VII.6.2.  A root is chosen for every `S`-unit, and those roots generate `M`
over `K`. -/
def SPthRoots
    (K M : Type u) [Field K] [Field M]
    [NumberField K] [Algebra K M]
    (p : ℕ) (S : Finset (NumberFieldPlace K)) : Prop :=
  ∃ root : ArithmeticSUnits K (finitePrimePart K S) → M,
    (∀ a, root a ^ p = algebraMap K M (((a : Kˣ) : K))) ∧
      IntermediateField.adjoin K (Set.range root) = ⊤

set_option synthInstance.maxHeartbeats 300000 in
-- Resolving the dependent product of local power-class groups requires a
-- deeper group-instance search.
/-- The finite-cardinality argument in the proof of Lemma 6.9.  This is a
general theorem about the actual map above: equality of the kernel index and
target cardinality forces surjectivity. -/
theorem obvious_numerical_inputs
    (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (S : Finset (NumberFieldPlace K))
    (T : Finset (FinitePrime K))
    (hDisjoint : ∀ P : FinitePrime K, P ∈ T →
      (Sum.inl P : NumberFieldPlace K) ∉ S)
    [Finite (localUnitClasses K p T)]
    (hkernelIndex :
      (obviousMap K p S T hDisjoint).ker.index = p ^ T.card)
    (htargetCard :
      Nat.card (localUnitClasses K p T) = p ^ T.card) :
    Function.Surjective (obviousMap K p S T hDisjoint) := by
  rw [← MonoidHom.range_eq_top]
  apply Subgroup.eq_top_of_card_eq
  rw [← Subgroup.index_ker (obviousMap K p S T hDisjoint)]
  exact hkernelIndex.trans htargetCard.symm

set_option synthInstance.maxHeartbeats 300000 in
-- Elaborating the kernel-index bridge requires the local power-class product
-- and its induced homomorphism instances.
/-- The first numerical input in Milne's proof.  It is deliberately stated
only for a set `T` carrying the Frobenius basis of Lemma 6.2 and for the
Kummer extension containing the chosen `p`th roots of the `S`-units.

Lemma 6.3 identifies this kernel with `U(S) ∩ Lˣᵖ`; Kummer theory then gives
its index as `[M : L] = p ^ T.card`. -/
def KummerIndexBridge : Prop :=
  ∀ (p : ℕ) (K L M : Type u)
    [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M]
    [IsGalois L M] [IsAbelianGalois K M],
    p.Prime → (primitiveRoots p K).Nonempty →
    ∀ (hexponent : ∀ sigma : Gal(M/K), sigma ^ p = 1)
      (S : Finset (NumberFieldPlace K)),
      (∀ Q : FinitePrime M,
        (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∉ S →
          Algebra.IsUnramifiedAt (OK K) Q.asIdeal) →
      ContainsPthRoots K M p S →
      SPthRoots K M p S →
      ∀ (T : Finset (FinitePrime K))
        (hDisjoint : ∀ P : FinitePrime K, P ∈ T →
          (Sum.inl P : NumberFieldPlace K) ∉ S),
        FrobeniusBasis
            (K := K) (L := L) (M := M) p hexponent S T →
          (obviousMap K p S T hDisjoint).ker.index = p ^ T.card

set_option synthInstance.maxHeartbeats 300000 in
-- The target-cardinality bridge contains a dependent product of local unit
-- quotients whose group structure needs deeper instance search.
/-- The second numerical input in Milne's proof.  Proposition 6.8 gives one
factor of `p` at every `P ∈ T`: disjointness and the assumption that `S`
contains every divisor of `p` imply `|p|_P = 1`.  The bridge includes the
finiteness needed to use the target's natural cardinality. -/
def LocalTargetBridge : Prop :=
  ∀ (p : ℕ) (K : Type u) [Field K] [NumberField K],
    p.Prime → (primitiveRoots p K).Nonempty →
    ∀ (S : Finset (NumberFieldPlace K)) (T : Finset (FinitePrime K)),
      (∀ v : NumberFieldPlace K,
        normalizedPlaceValue K v (p : K) ≠ 1 → v ∈ S) →
      (∀ P : FinitePrime K, P ∈ T →
        (Sum.inl P : NumberFieldPlace K) ∉ S) →
      Finite (localUnitClasses K p T) ∧
        Nat.card (localUnitClasses K p T) = p ^ T.card

set_option synthInstance.maxHeartbeats 300000 in
-- The source statement combines both dependent local power-class bridges and
-- their quotient-group structures.
set_option synthInstance.maxHeartbeats 300000 in
-- Applying the two numerical bridges requires resolving the same dependent
-- local quotient group in the assembled proof.
/-- Lemma 6.9 follows from exactly the two cardinality computations in the
printed proof. -/
theorem pth_roots_bridges
    (hkernel : KummerIndexBridge.{u})
    (htarget : LocalTargetBridge.{u}) :
    (∀ (p : ℕ) (K L M : Type u)
          [Field K] [Field L] [Field M]
          [NumberField K] [NumberField L] [NumberField M]
          [Algebra K L] [Algebra L M] [Algebra K M]
          [IsScalarTower K L M]
          [FiniteDimensional K L] [FiniteDimensional L M]
          [IsGalois L M] [IsAbelianGalois K M],
          p.Prime → (primitiveRoots p K).Nonempty →
          ∀ (hexponent : ∀ sigma : Gal(M/K), sigma ^ p = 1)
            (S : Finset (NumberFieldPlace K)),
            (∀ v : NumberFieldPlace K,
              normalizedPlaceValue K v (p : K) ≠ 1 → v ∈ S) →
            (∀ Q : FinitePrime M,
              (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∉ S →
                Algebra.IsUnramifiedAt (OK K) Q.asIdeal) →
            ContainsPthRoots K M p S →
            SPthRoots K M p S →
            ∀ (T : Finset (FinitePrime K))
              (hDisjoint : ∀ P : FinitePrime K, P ∈ T →
                (Sum.inl P : NumberFieldPlace K) ∉ S),
              FrobeniusBasis
                  (K := K) (L := L) (M := M) p hexponent S T →
                Function.Surjective (obviousMap K p S T hDisjoint)) := by
  intro p K L M _fieldK _fieldL _fieldM _numberFieldK _numberFieldL
    _numberFieldM _algebraKL _algebraLM _algebraKM _tower _finiteKL
    _finiteLM _galoisLM _abelianKM hp hroots hexponent S hDividing
    hunramified hcontains hgenerate T hDisjoint hT
  rcases htarget p K hp hroots S T hDividing hDisjoint with
    ⟨hfinite, htargetCard⟩
  letI : Finite (localUnitClasses K p T) := hfinite
  apply obvious_numerical_inputs
    K p S T hDisjoint
  · exact hkernel p K L M hp hroots hexponent S hunramified hcontains hgenerate
      T hDisjoint hT
  · exact htargetCard

end

end Submission.CField.KNIndex
