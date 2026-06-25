import Submission.ClassField.KummerNormIndex.LocalSplitting
import Submission.ClassField.KummerNormIndex.LocalNormBridges

/-!
# The local norm assembly in Proposition VII.6.10

The split, power, and unramified-unit local cases are assembled into one
actual idèle norm preimage.  The remaining input is precisely the
unramifiedness criterion of Proposition VII.A.5 for the simple radical
extension outside `S ∪ T`.
-/

namespace Submission.CField.KNIndex

open Filter IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.KTheory
open Submission.CField.NIndex
open Submission.CField.HNorm
open scoped RestrictedProduct

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

/-- The Appendix A.5 input in exactly the one-generator form needed in
Proposition VII.6.10. -/
def OutsideUnramifiedBridge : Prop :=
  ∀ (n : ℕ) (K : Type u) [Field K] [NumberField K]
    (b : Kˣ) (S : Finset (NumberFieldPlace K))
    (T : Finset (FinitePrime K))
    (_hDividing : ∀ v : NumberFieldPlace K,
      normalizedPlaceValue K v (n : K) ≠ 1 → v ∈ S)
    (_hUnit : nthPlaceOutside K b S T)
    (data : KEData K n b),
    letI : Field data.L := data.fieldL
    letI : NumberField data.L := data.numberFieldL
    letI : Algebra K data.L := data.algebraKL
    ∀ P : FinitePrime K,
      (Sum.inl P : NumberFieldPlace K) ∉ combinedPlaces K S T →
      ∀ Q : FinitePrime data.L, Q.under (OK K) = P →
        Algebra.IsUnramifiedAt (OK K) Q.asIdeal

set_option synthInstance.maxHeartbeats 1000000 in
-- Resolving the Kummer extension and all finite/infinite local norm maps
-- requires a deeper dependent instance search.
set_option maxHeartbeats 6000000 in
-- The proof assembles the split, power, and unramified local norm cases over
-- every idèle coordinate.
/-- The three local norm cases imply the local-norm bridge of Proposition
VII.6.10. -/
theorem bridge_outside_unramified
    (houtside : OutsideUnramifiedBridge.{u}) :
    LocalNormBridge.{u} := by
  classical
  intro n K _ _ b hroots S T hInfinite hDividing hDisjoint hLocal hUnit data
  letI : Field data.L := data.fieldL
  letI : NumberField data.L := data.numberFieldL
  letI : Algebra K data.L := data.algebraKL
  letI : FiniteDimensional K data.L := data.finiteDimensionalKL
  letI : IsGalois K data.L := data.isGaloisKL
  have hn : 0 < n := by
    apply Nat.pos_of_ne_zero
    intro hn
    subst n
    simp [primitiveRoots_zero] at hroots
  let zeta := hroots.choose
  have hzeta : IsPrimitiveRoot zeta n :=
    (mem_primitiveRoots hn).mp hroots.choose_spec
  have hpowRoot : ∀ x ∈ ({data.root} : Set data.L),
      x ^ n ∈ Set.range (algebraMap K data.L) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨(b : K), data.root_pow.symm⟩
  letI : IsMulCommutative Gal(data.L/K) :=
    ⟨⟨fun sigma tau ↦ aut_commute_nth hn hzeta
      {data.root} data.adjoin_root_top hpowRoot sigma tau⟩⟩
  letI : IsAbelianGalois K data.L :=
    { toIsGalois := inferInstance
      toIsMulCommutative := inferInstance }
  have hexponent : ∀ sigma : Gal(data.L/K), sigma ^ n = 1 :=
    aut_nth_roots hn hzeta {data.root}
      data.adjoin_root_top hpowRoot
  have hpowerCases := powerLocalBridge n K data.L hexponent
  rintro a ⟨d, hd, rfl⟩
  have hFiniteLift : ∀ P : FinitePrime K,
      ∃ z : ∀ Q : FinitePrime data.L, (Q.adicCompletion data.L)ˣ,
        (∀ Q, Q.under (OK K) ≠ P → z Q = 1) ∧
        (∏ Q, finiteCompletionNorm (K := K) (L := data.L) P Q
          (z (upperPrime (K := K) (L := data.L) P Q))) = d.1.2.1 P ∧
        ((Sum.inl P : NumberFieldPlace K) ∉ S → P ∉ T →
          ∀ Q, z Q ∈ IdeleUnitSubgroup (OK data.L) data.L Q) := by
    intro P
    by_cases hPS : (Sum.inl P : NumberFieldPlace K) ∈ S
    · have hsplit := place_splits_completely
        n K b hroots data P (hLocal (Sum.inl P) hPS)
      let Q := chosenPrimeFactor (K := K) (L := data.L) P
      have hsurj := surjective_splits_completely
        P Q hsplit
      obtain ⟨y, hy⟩ := hsurj (d.1.2.1 P)
      obtain ⟨z, hzSupport, hzNorm⟩ :=
        lift_completion_range
          P Q (d.1.2.1 P) ⟨y, hy⟩
      exact ⟨z, hzSupport, hzNorm, fun h ↦ (h hPS).elim⟩
    · by_cases hPT : P ∈ T
      · let PT : T := ⟨P, hPT⟩
        have hdP := congrFun (show
          restrictedIdeleClass K n S T hDisjoint d = 1
            from hd) PT
        rw [Pi.one_apply] at hdP
        have hdPower :
            restrictedIdeleHom
                K S T hDisjoint PT d ∈
              pthPowerSubgroup n (P.adicCompletionIntegers K)ˣ :=
          (QuotientGroup.eq_one_iff _).mp hdP
        obtain ⟨y, hy⟩ := hdPower
        have hfieldPower : d.1.2.1 P ∈
            pthPowerSubgroup n (P.adicCompletion K)ˣ := by
          refine ⟨Units.map
            (P.adicCompletionIntegers K).subtype.toMonoidHom y, ?_⟩
          apply Units.ext
          exact congrArg (fun z : (P.adicCompletionIntegers K)ˣ ↦
            (((z : P.adicCompletionIntegers K) : P.adicCompletion K))) hy
        obtain ⟨z, hzSupport, hzNorm⟩ := hpowerCases.1 P _ hfieldPower
        exact ⟨z, hzSupport, hzNorm, fun _ h ↦ (h hPT).elim⟩
      · have hPCombined :
            (Sum.inl P : NumberFieldPlace K) ∉ combinedPlaces K S T := by
          intro h
          rcases Finset.mem_union.mp h with h | h
          · exact hPS h
          · rcases Finset.mem_image.mp h with ⟨Q, hQT, hQP⟩
            exact hPT ((Sum.inl_injective hQP) ▸ hQT)
        have hUpper : ∀ Q : UpperPrimeFactors (K := K) (L := data.L) P,
            Algebra.IsUnramifiedAt (OK K)
              (upperPrime (K := K) (L := data.L) P Q).asIdeal := by
          intro Q
          exact houtside n K b S T hDividing hUnit data P hPCombined
            (upperPrime (K := K) (L := data.L) P Q)
            (upperPrime_under (K := K) (L := data.L) P Q)
        obtain ⟨z, hzSupport, hzUnits, hzNorm⟩ :=
          unramifiedUnitBridge K data.L P hUpper (d.1.2.1 P)
            (d.2 P hPS)
        exact ⟨z, hzSupport, hzNorm, fun _ _ ↦ hzUnits⟩
  choose zFinite hzFiniteSupport hzFiniteNorm hzFiniteUnits using hFiniteLift
  let upperFinite : ∀ Q : FinitePrime data.L, (Q.adicCompletion data.L)ˣ :=
    fun Q ↦ zFinite (Q.under (OK K)) Q
  let exceptional : Finset (FinitePrime data.L) :=
    finiteAboveBase (K := K) (M := data.L)
      (S ∪ T.image (fun P ↦ (Sum.inl P : NumberFieldPlace K)))
  have hFiniteRestricted : ∀ᶠ Q in Filter.cofinite,
      upperFinite Q ∈ IdeleUnitSubgroup (OK data.L) data.L Q := by
    rw [Filter.eventually_cofinite]
    refine exceptional.finite_toSet.subset ?_
    intro Q hQnotUnit
    by_contra hQexceptional
    apply hQnotUnit
    have hQnotST : (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∉
        S ∪ T.image (fun P ↦ (Sum.inl P : NumberFieldPlace K)) := by
      change Q ∉ finiteAboveBase (K := K) (M := data.L) _ at hQexceptional
      rwa [primes_above_base] at hQexceptional
    have hQnotS : (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∉ S :=
      fun h ↦ hQnotST (Finset.mem_union_left _ h)
    have hQnotT : Q.under (OK K) ∉ T := fun h ↦ hQnotST
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, h, rfl⟩))
    exact hzFiniteUnits _ hQnotS hQnotT Q
  let xFinite : FiniteIdeles (OK data.L) data.L :=
    RestrictedProduct.mk upperFinite hFiniteRestricted
  have hFiniteNorm : finiteIdeleNorm (K := K) (L := data.L) xFinite = d.1.2 := by
    apply RestrictedProduct.ext
    intro P
    change (∏ Q, finiteCompletionNorm (K := K) (L := data.L) P Q
      (upperFinite (upperPrime (K := K) (L := data.L) P Q))) = d.1.2.1 P
    simpa only [upperFinite, upperPrime_under] using hzFiniteNorm P
  have hInfiniteLift : ∀ v : InfinitePlace K,
      InfiniteNormLift K data.L v (MulEquiv.piUnits d.1.1 v) := by
    intro v
    let w := chosenUpperPlace (K := K) (L := data.L) v
    exact infinite_lift_surjective v w
      (infinite_completion_surjective n K b hroots data v
        (hLocal (Sum.inr v) (hInfinite v)) w) _
  choose zInfinite hzInfiniteSupport hzInfiniteNorm using hInfiniteLift
  let upperInfinite : ∀ w : InfinitePlace data.L, w.Completionˣ :=
    fun w ↦ zInfinite (w.comap (algebraMap K data.L)) w
  let xInfinite : (InfiniteAdeleRing data.L)ˣ :=
    MulEquiv.piUnits.symm upperInfinite
  have hInfiniteNorm : infiniteIdeleNorm (K := K) (L := data.L) xInfinite = d.1.1 := by
    apply MulEquiv.piUnits.injective
    funext v
    rw [infinite_idele, infinite_norm]
    have hxInfinite : MulEquiv.piUnits xInfinite = upperInfinite :=
      MulEquiv.apply_symm_apply _ _
    rw [hxInfinite]
    rw [← hzInfiniteNorm v]
    let f : InfinitePlacesAbove (K := K) (L := data.L) v → v.Completionˣ :=
      fun w ↦ infiniteCompletionNorm (K := K) (L := data.L) v w
        (zInfinite (w.1.comap (algebraMap K data.L)) w.1)
    let g : InfinitePlacesAbove (K := K) (L := data.L) v → v.Completionˣ :=
      fun w ↦ infiniteCompletionNorm (K := K) (L := data.L) v w
        (zInfinite v w.1)
    exact @Fintype.prod_equiv _ _ _
      (Submission.CField.Ideles.infinitePlacesAboveFintype v)
      (infinitePlacesAboveFintype K data.L v) inferInstance
      (Equiv.refl _) f g (by
        intro w
        dsimp only [f, g]
        rw [w.2]
        rfl)
  exact ⟨(xInfinite, xFinite), Prod.ext hInfiniteNorm hFiniteNorm⟩

end

end Submission.CField.KNIndex
