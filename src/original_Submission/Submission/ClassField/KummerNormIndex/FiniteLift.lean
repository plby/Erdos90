import Submission.ClassField.KummerNormIndex.GalMLMK
import Submission.ClassField.KummerNormIndex.IdeleSubgroup

/-!
# Chapter VII, Section 6, Lemma 6.4

For the sets `S` and `T` chosen in the Kummer argument, let `E` be the
subgroup of the actual idèle group whose coordinates are `p`th powers at
places in `S`, arbitrary at the finite primes in `T`, and local units at the
remaining finite primes.  Lemma 6.4 says that `E` is contained in the actual
idèle norm range from `L`.

The proof below performs the restricted-product assembly.  Its only bridges
are the three local inputs in the printed proof: exponent-`p` local class
field theory at `S`, local triviality at `T`, and surjectivity of the unit
norm in an unramified extension outside `S ∪ T`.
-/

namespace Submission.CField.KNIndex

open Filter IsDedekindDomain NumberField
open scoped RestrictedProduct
open Submission.NumberTheory.Milne
open Submission.CField.Ideles

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

/-- A simultaneous choice of norm preimages in the completed fields above
one finite base prime.  This is a genuinely local assertion: the index is
the finite fiber over the single prime `P`. -/
def FiniteNormLift
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (P : FinitePrime K) (x : (P.adicCompletion K)ˣ) : Prop :=
  ∃ z : ∀ Q : FinitePrime L, (Q.adicCompletion L)ˣ,
    (∀ Q, Q.under (OK K) ≠ P → z Q = 1) ∧
    (∏ Q, finiteCompletionNorm (K := K) (L := L) P Q
      (z (upperPrime (K := K) (L := L) P Q))) = x

/-- The unit-preserving form of the preceding local norm lift. -/
def UnitNormLift
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (P : FinitePrime K) (x : (P.adicCompletion K)ˣ) : Prop :=
  ∃ z : ∀ Q : FinitePrime L, (Q.adicCompletion L)ˣ,
    (∀ Q, Q.under (OK K) ≠ P → z Q = 1) ∧
    (∀ Q, z Q ∈ IdeleUnitSubgroup (OK L) L Q) ∧
    (∏ Q, finiteCompletionNorm (K := K) (L := L) P Q
      (z (upperPrime (K := K) (L := L) P Q))) = x

noncomputable local instance infinitePlacesAboveFintype
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (v : InfinitePlace K) :
    Fintype (InfinitePlacesAbove (K := K) (L := L) v) := by
  exact infiniteCor84ExtensionsFintype v

/-- A simultaneous choice of norm preimages in the archimedean completions
above one infinite place. -/
def InfiniteNormLift
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (v : InfinitePlace K) (x : v.Completionˣ) : Prop :=
  ∃ z : ∀ w : InfinitePlace L, w.Completionˣ,
    (∀ w, w.comap (algebraMap K L) ≠ v → z w = 1) ∧
    (∏ w, infiniteCompletionNorm (K := K) (L := L) v w (z w.1)) = x

/-- The local-class-field-theory input at the places in `S`: because the
local Galois group is killed by `p`, every `p`th power is a local norm.
Both finite and infinite completions are included. -/
def PowerLocalBridge : Prop :=
  ∀ (p : ℕ) (K L : Type u)
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L],
    (∀ sigma : Gal(L/K), sigma ^ p = 1) →
      (∀ (P : FinitePrime K) (x : (P.adicCompletion K)ˣ),
        x ∈ pthPowerSubgroup p (P.adicCompletion K)ˣ →
          FiniteNormLift K L P x) ∧
      (∀ (v : InfinitePlace K) (x : v.Completionˣ),
        x ∈ pthPowerSubgroup p v.Completionˣ →
          InfiniteNormLift K L v x)

/-- Proposition III.1.2 in the concrete completion coordinates used by the
idèle norm: at an unramified finite prime, every local unit has a norm lift
consisting of upper local units. -/
def UnramifiedUnitBridge : Prop :=
  ∀ (K L : Type u)
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (P : FinitePrime K),
    (∀ Q : UpperPrimeFactors (K := K) (L := L) P,
      Algebra.IsUnramifiedAt (OK K)
        (upperPrime (K := K) (L := L) P Q).asIdeal) →
      ∀ x : (P.adicCompletion K)ˣ,
        x ∈ IdeleUnitSubgroup (OK K) K P →
          UnitNormLift K L P x

/-- The preceding sentence after Lemma 6.2, `L_w = K_v` for `v ∈ T`,
expressed in exactly the local norm form used in Lemma 6.4. -/
def SelectedLocallyTrivial
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (T : Finset (FinitePrime K)) : Prop :=
  ∀ P : FinitePrime K, P ∈ T →
    ∀ x : (P.adicCompletion K)ˣ, FiniteNormLift K L P x

set_option synthInstance.maxHeartbeats 300000 in
-- Constructing the global restricted-product preimage uses dependent local
-- completion coordinates at every finite and infinite place.
set_option maxHeartbeats 2000000 in
/-- Lemma 6.4 follows by assembling the three local norm cases into an actual
idèle of `L`.  No global norm-surjectivity assumption is used here. -/
theorem lift_local_cases
    (hpower : PowerLocalBridge.{u})
    (hunramifiedUnit : UnramifiedUnitBridge.{u}) :
    (∀ (p : ℕ) (K L : Type u)
          [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L],
          (∀ sigma : Gal(L/K), sigma ^ p = 1) →
          ∀ (S : Finset (NumberFieldPlace K)) (T : Finset (FinitePrime K)),
            (∀ v : InfinitePlace K,
              (Sum.inr v : NumberFieldPlace K) ∈ S) →
            SelectedLocallyTrivial K L T →
            (∀ Q : FinitePrime L,
              (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∉ S →
                Algebra.IsUnramifiedAt (OK K) Q.asIdeal) →
            ideleSubgroup K p S T ≤
              ideleNormSubgroup (K := K) (L := L)) := by
  classical
  intro p K L _ _ _ _ _ _ _ hexponent S T hSinfinite hTtrivial hunramified a ha
  have hpowerCases := hpower p K L hexponent
  have hFiniteLift : ∀ P : FinitePrime K,
      ∃ z : ∀ Q : FinitePrime L, (Q.adicCompletion L)ˣ,
        (∀ Q, Q.under (OK K) ≠ P → z Q = 1) ∧
        (∏ Q, finiteCompletionNorm (K := K) (L := L) P Q
          (z (upperPrime (K := K) (L := L) P Q))) = a.2.1 P ∧
        ((Sum.inl P : NumberFieldPlace K) ∉ S → P ∉ T →
          ∀ Q, z Q ∈ IdeleUnitSubgroup (OK L) L Q) := by
    intro P
    by_cases hPS : (Sum.inl P : NumberFieldPlace K) ∈ S
    · obtain ⟨z, hzSupport, hzNorm⟩ :=
          hpowerCases.1 P (a.2.1 P) (ha.2.1 P hPS)
      refine ⟨z, hzSupport, hzNorm, ?_⟩
      intro hPnotS
      exact (hPnotS hPS).elim
    · by_cases hPT : P ∈ T
      · obtain ⟨z, hzSupport, hzNorm⟩ := hTtrivial P hPT (a.2.1 P)
        refine ⟨z, hzSupport, hzNorm, ?_⟩
        intro _ hPnotT
        exact (hPnotT hPT).elim
      · have hUpperUnramified : ∀ Q : UpperPrimeFactors (K := K) (L := L) P,
            Algebra.IsUnramifiedAt (OK K)
              (upperPrime (K := K) (L := L) P Q).asIdeal := by
          intro Q
          apply hunramified (upperPrime (K := K) (L := L) P Q)
          simpa only [upperPrime_under] using hPS
        obtain ⟨z, hzSupport, hzUnits, hzNorm⟩ :=
          hunramifiedUnit K L P hUpperUnramified (a.2.1 P)
            (ha.2.2 P hPS hPT)
        exact ⟨z, hzSupport, hzNorm, fun _ _ ↦ hzUnits⟩
  choose zFinite hzFiniteSupport hzFiniteNorm hzFiniteUnits using hFiniteLift
  let upperFinite : ∀ Q : FinitePrime L, (Q.adicCompletion L)ˣ :=
    fun Q ↦ zFinite (Q.under (OK K)) Q
  let exceptional : Finset (FinitePrime L) :=
    finiteAboveBase (K := K) (M := L)
      (S ∪ T.image (fun P ↦ (Sum.inl P : NumberFieldPlace K)))
  have hFiniteRestricted : ∀ᶠ Q in Filter.cofinite,
      upperFinite Q ∈ IdeleUnitSubgroup (OK L) L Q := by
    rw [Filter.eventually_cofinite]
    refine exceptional.finite_toSet.subset ?_
    intro Q hQnotUnit
    by_contra hQexceptional
    apply hQnotUnit
    have hQnotST :
        (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∉
          S ∪ T.image (fun P ↦ (Sum.inl P : NumberFieldPlace K)) := by
      have hQexceptional' : Q ∉ exceptional := hQexceptional
      change Q ∉ finiteAboveBase (K := K) (M := L)
        (S ∪ T.image (fun P ↦ (Sum.inl P : NumberFieldPlace K))) at hQexceptional'
      rw [primes_above_base] at hQexceptional'
      exact hQexceptional'
    have hQnotS :
        (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∉ S := by
      intro hQS
      exact hQnotST (Finset.mem_union_left _ hQS)
    have hQnotT : Q.under (OK K) ∉ T := by
      intro hQT
      apply hQnotST
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨Q.under (OK K), hQT, rfl⟩
    simpa only [upperFinite] using
      hzFiniteUnits (Q.under (OK K)) hQnotS hQnotT Q
  let xFinite : FiniteIdeles (OK L) L :=
    RestrictedProduct.mk upperFinite hFiniteRestricted
  have hFiniteNorm : finiteIdeleNorm (K := K) (L := L) xFinite = a.2 := by
    apply RestrictedProduct.ext
    intro P
    change (∏ Q : UpperPrimeFactors (K := K) (L := L) P,
      finiteCompletionNorm (K := K) (L := L) P Q
        (upperFinite (upperPrime (K := K) (L := L) P Q))) = a.2.1 P
    calc
      _ = ∏ Q : UpperPrimeFactors (K := K) (L := L) P,
          finiteCompletionNorm (K := K) (L := L) P Q
            (zFinite P (upperPrime (K := K) (L := L) P Q)) := by
        apply Finset.prod_congr rfl
        intro Q _
        congr 1
        change zFinite
            ((upperPrime (K := K) (L := L) P Q).under (OK K))
            (upperPrime (K := K) (L := L) P Q) = _
        rw [upperPrime_under]
      _ = a.2.1 P := hzFiniteNorm P
  have hInfiniteLift : ∀ v : InfinitePlace K,
      InfiniteNormLift K L v (MulEquiv.piUnits a.1 v) := by
    intro v
    exact hpowerCases.2 v (MulEquiv.piUnits a.1 v)
      (ha.1 v (hSinfinite v))
  choose zInfinite hzInfiniteSupport hzInfiniteNorm using hInfiniteLift
  let upperInfinite : ∀ w : InfinitePlace L, w.Completionˣ :=
    fun w ↦ zInfinite (w.comap (algebraMap K L)) w
  let xInfinite : (InfiniteAdeleRing L)ˣ :=
    MulEquiv.piUnits.symm upperInfinite
  have hInfiniteNorm : infiniteIdeleNorm (K := K) (L := L) xInfinite = a.1 := by
    apply MulEquiv.piUnits.injective
    funext v
    rw [infinite_idele, infinite_norm]
    change (∏ w : InfinitePlacesAbove (K := K) (L := L) v,
      infiniteCompletionNorm (K := K) (L := L) v w
        (upperInfinite w.1)) = MulEquiv.piUnits a.1 v
    calc
      _ = ∏ w : InfinitePlacesAbove (K := K) (L := L) v,
          infiniteCompletionNorm (K := K) (L := L) v w
            (zInfinite v w.1) := by
        apply Finset.prod_congr rfl
        intro w _
        congr 1
        change zInfinite (w.1.comap (algebraMap K L)) w.1 =
          zInfinite v w.1
        rw [w.2]
      _ = MulEquiv.piUnits a.1 v := hzInfiniteNorm v
  refine ⟨(xInfinite, xFinite), ?_⟩
  exact Prod.ext hInfiniteNorm hFiniteNorm

end

end Submission.CField.KNIndex
