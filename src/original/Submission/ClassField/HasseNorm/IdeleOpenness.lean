import Submission.ClassField.KummerNormIndex.FiniteLift
import Submission.ClassField.KummerNormIndex.PowerIndex
import Submission.ClassField.Ideles.ModulusUnitSubgroup
import Submission.ClassField.HasseNorm.FinitePlaceBridge
import Submission.ClassField.HasseNorm.LocalOpenness
import Submission.ClassField.HasseNorm.UnramifiedLocal
import Submission.ClassField.HasseNorm.InfiniteBasicSubgroup
import Submission.NumberTheory.Ramification.RamificationDiscriminant
import Submission.NumberTheory.Locals.UnramifiedExtensions

/-!
# Openness of the idèle norm subgroup

The finite-place argument is the restricted-product form of Proposition
V.4.12.  At the finitely many ramified base primes we use openness of the
corresponding completed norm group.  Away from those primes, unramifiedness
makes every local unit a norm of an upper local unit.  These local lifts
assemble to an actual finite idèle.
-/

namespace Submission.CField.HNorm

open Filter Ideal IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.LFTheory
open Submission.CField.Ideles
open Submission.CField.KNIndex
open scoped RestrictedProduct Topology

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

variable {K L : Type u} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- A number field is small enough to have a Type-0 model: its finite
`ℚ`-basis embeds it into a finite power of `ℚ`. -/
private theorem number_small_zero
    (F : Type u) [Field F] [NumberField F] : Small.{0} F := by
  let b := Module.finBasis ℚ F
  exact small_of_injective b.repr.injective

/-- Uniform completion preserves Type-0 smallness.  We spell this out via
the set-of-sets representation of filters because `Completion` has no generic
`Small` instance. -/
private theorem uniform_small_zero
    (X : Type u) [Small.{0} X] [UniformSpace X] :
    Small.{0} (UniformSpace.Completion X) := by
  let eSet : Set X ≃ Set (Shrink.{0} X) :=
    Equiv.Set.congr (equivShrink X)
  let eSetSet : Set (Set X) ≃ Set (Set (Shrink.{0} X)) :=
    Equiv.Set.congr eSet
  letI : Small.{0} (Set (Set X)) :=
    small_of_injective eSetSet.injective
  letI : Small.{0} (Filter X) := by
    apply small_of_injective (f := fun f : Filter X ↦ f.sets)
    intro f g h
    apply Filter.ext
    intro s
    change f.sets = g.sets at h
    change s ∈ f.sets ↔ s ∈ g.sets
    rw [h]
  letI : Small.{0} (CauchyFilter X) :=
    small_of_injective Subtype.val_injective
  change Small.{0} (Quotient (inseparableSetoid (CauchyFilter X)))
  exact small_of_surjective Quotient.mk_surjective

noncomputable local instance ideleNormOpennessInfinitePlacesAboveFintype
    (v : InfinitePlace K) :
    Fintype (InfinitePlacesAbove (K := K) (L := L) v) :=
  infiniteCor84ExtensionsFintype v

set_option synthInstance.maxHeartbeats 300000 in
-- Resolving the prime-adic completion norm and its local-field topology
-- requires a deeper instance search.
set_option maxHeartbeats 2000000 in
-- Openness of the local norm range transports the Type-0 local theorem
-- through the canonical completion models.
set_option maxRecDepth 100000 in
omit [FiniteDimensional K L] in
/-- The range of a norm between two prime-adic completion factors is open. -/
theorem completion_range_open
    (P : FinitePrime K)
    (Q : UpperPrimeFactors (K := K) (L := L) P) :
    IsOpen ((finiteCompletionNorm (K := K) (L := L) P Q).range :
      Set (P.adicCompletion K)ˣ) := by
  let F := P.adicCompletion K
  let q := upperPrime (K := K) (L := L) P Q
  let E := q.adicCompletion L
  letI : Small.{0} K := number_small_zero K
  letI : Small.{0} L := number_small_zero L
  letI : Small.{0} (WithVal (P.valuation K)) :=
    small_of_injective (WithVal.equiv (P.valuation K)).injective
  letI : Small.{0} (WithVal (q.valuation L)) :=
    small_of_injective (WithVal.equiv (q.valuation L)).injective
  letI : Small.{0} F := uniform_small_zero _
  letI : Small.{0} E := uniform_small_zero _
  let hP : P.asIdeal.map (algebraMap (OK K) (OK L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot P.ne_bot
  letI : Algebra F E :=
    adicFactorAlgebra (K := K) (L := L) P hP Q
  letI : Module.Finite F E :=
    finite_completion_module (K := K) (L := L) P Q
  letI : NontriviallyNormedField F :=
    adicNontriviallyNormed P
  letI : CharZero F :=
    (RingHom.charZero_iff (algebraMap K F).injective).mp inferInstance
  letI : IsUltrametricDist F := by infer_instance
  letI : ValuativeRel F := adicValuativeRel P
  letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
  letI : IsNonarchimedeanLocalField F :=
    adicNonarchimedeanField P
  change IsOpen (normSubgroup F E : Set Fˣ)
  exact subgroup_open_small F E

/-- Membership in one completed norm range gives a lift supported at that
single upper prime. -/
theorem lift_completion_range
    (P : FinitePrime K)
    (Q : UpperPrimeFactors (K := K) (L := L) P)
    (x : (P.adicCompletion K)ˣ)
    (hx : x ∈ (finiteCompletionNorm (K := K) (L := L) P Q).range) :
    FiniteNormLift K L P x := by
  classical
  obtain ⟨y, hy⟩ := hx
  let q := upperPrime (K := K) (L := L) P Q
  let z : ∀ R : FinitePrime L, (R.adicCompletion L)ˣ :=
    Pi.mulSingle (M := fun R : FinitePrime L ↦ (R.adicCompletion L)ˣ) q y
  refine ⟨z, ?_, ?_⟩
  · intro R hR
    apply Pi.mulSingle_eq_of_ne
      (M := fun R : FinitePrime L ↦ (R.adicCompletion L)ˣ)
    intro hRq
    apply hR
    rw [hRq, upperPrime_under]
  · rw [Finset.prod_eq_single Q]
    · change finiteCompletionNorm (K := K) (L := L) P Q (z q) = x
      have hzq : z q = y := Pi.mulSingle_eq_same
        (M := fun R : FinitePrime L ↦ (R.adicCompletion L)ˣ) q y
      rw [hzq]
      exact hy
    · intro Q' _ hQ'
      have hUpper : upperPrime (K := K) (L := L) P Q' ≠ q := by
        intro h
        apply hQ'
        apply upper_factor_injective
          (K := K) (L := L) P
        apply Subtype.ext
        exact h
      change finiteCompletionNorm (K := K) (L := L) P Q'
        (z (upperPrime (K := K) (L := L) P Q')) = 1
      have hzQ : z (upperPrime (K := K) (L := L) P Q') = 1 :=
        Pi.mulSingle_eq_of_ne
          (M := fun R : FinitePrime L ↦ (R.adicCompletion L)ˣ) hUpper y
      rw [hzQ]
      exact map_one _
    · intro hQ
      exact (hQ (Finset.mem_univ Q)).elim

/-- At an unramified prime, the preceding one-coordinate lift can be chosen
to consist entirely of upper local units. -/
theorem norm_lift_unramified
    (P : FinitePrime K)
    (Q : UpperPrimeFactors (K := K) (L := L) P)
    (hQ : Algebra.IsUnramifiedAt (OK K)
      (upperPrime (K := K) (L := L) P Q).asIdeal)
    (x : (P.adicCompletion K)ˣ)
    (hx : x ∈ IdeleUnitSubgroup (OK K) K P) :
    UnitNormLift K L P x := by
  classical
  obtain ⟨y, hy⟩ :=
    units_surjective_unramified
      (K := K) (L := L) P Q hQ ⟨x, hx⟩
  let q := upperPrime (K := K) (L := L) P Q
  let z : ∀ R : FinitePrime L, (R.adicCompletion L)ˣ :=
    Pi.mulSingle (M := fun R : FinitePrime L ↦ (R.adicCompletion L)ˣ) q y.1
  refine ⟨z, ?_, ?_, ?_⟩
  · intro R hR
    apply Pi.mulSingle_eq_of_ne
      (M := fun R : FinitePrime L ↦ (R.adicCompletion L)ˣ)
    intro hRq
    apply hR
    rw [hRq, upperPrime_under]
  · intro R
    by_cases hRq : R = q
    · subst R
      simpa only [z, Pi.mulSingle_eq_same] using y.2
    · have hzR : z R = 1 := Pi.mulSingle_eq_of_ne
          (M := fun R : FinitePrime L ↦ (R.adicCompletion L)ˣ) hRq y.1
      rw [hzR]
      exact (IdeleUnitSubgroup (OK L) L R).one_mem
  · rw [Finset.prod_eq_single Q]
    · change finiteCompletionNorm (K := K) (L := L) P Q (z q) = x
      have hzq : z q = y.1 := Pi.mulSingle_eq_same
        (M := fun R : FinitePrime L ↦ (R.adicCompletion L)ˣ) q y.1
      rw [hzq]
      exact hy
    · intro Q' _ hQ'
      have hUpper : upperPrime (K := K) (L := L) P Q' ≠ q := by
        intro h
        apply hQ'
        apply upper_factor_injective
          (K := K) (L := L) P
        apply Subtype.ext
        exact h
      change finiteCompletionNorm (K := K) (L := L) P Q'
        (z (upperPrime (K := K) (L := L) P Q')) = 1
      have hzQ : z (upperPrime (K := K) (L := L) P Q') = 1 :=
        Pi.mulSingle_eq_of_ne
          (M := fun R : FinitePrime L ↦ (R.adicCompletion L)ˣ) hUpper y.1
      rw [hzQ]
      exact map_one _
    · intro hQmem
      exact (hQmem (Finset.mem_univ Q)).elim

/-- Choose one completion factor above each finite base prime. -/
noncomputable def chosenPrimeFactor
    (P : FinitePrime K) :
    UpperPrimeFactors (K := K) (L := L) P := by
  let q : P.asIdeal.primesOver (OK L) := Classical.choice inferInstance
  exact ⟨q.1, (IsDedekindDomain.mem_primesOverFinset_iff (B := OK L) P.ne_bot).2 q.2⟩

/-- The standard open finite-idèle subgroup used in the norm proof: every
coordinate is a unit, with the finitely many exceptional coordinates also
required to lie in a chosen local norm range. -/
def ideleBasicSubgroup
    (T : Finset (FinitePrime K))
    (Q : ∀ P : FinitePrime K,
      UpperPrimeFactors (K := K) (L := L) P) :
    Subgroup (FiniteIdeles (OK K) K) where
  carrier := {a |
    (∀ P, a.1 P ∈ IdeleUnitSubgroup (OK K) K P) ∧
    (∀ P, P ∈ T →
      a.1 P ∈ (finiteCompletionNorm (K := K) (L := L) P (Q P)).range)}
  one_mem' := by
    exact ⟨fun P ↦ (IdeleUnitSubgroup (OK K) K P).one_mem,
      fun P _ ↦ (finiteCompletionNorm (K := K) (L := L) P (Q P)).range.one_mem⟩
  mul_mem' := by
    rintro a b ⟨haU, haN⟩ ⟨hbU, hbN⟩
    exact ⟨fun P ↦ (IdeleUnitSubgroup (OK K) K P).mul_mem
        (haU P) (hbU P),
      fun P hP ↦ (finiteCompletionNorm (K := K) (L := L) P (Q P)).range.mul_mem
        (haN P hP) (hbN P hP)⟩
  inv_mem' := by
    rintro a ⟨haU, haN⟩
    exact ⟨fun P ↦ (IdeleUnitSubgroup (OK K) K P).inv_mem (haU P),
      fun P hP ↦ (finiteCompletionNorm (K := K) (L := L) P (Q P)).range.inv_mem
        (haN P hP)⟩

private theorem idele_unit_open
    (P : FinitePrime K) :
    IsOpen (IdeleUnitSubgroup (OK K) K P :
      Set (P.adicCompletion K)ˣ) := by
  apply Submonoid.isOpen_units
  change IsOpen (P.adicCompletionIntegers K : Set (P.adicCompletion K))
  exact Valued.isOpen_valuationSubring _

omit [FiniteDimensional K L] in
/-- The finite conditions defining `ideleBasicSubgroup` are open
in the restricted-product topology. -/
theorem idele_basic_open
    (T : Finset (FinitePrime K))
    (Q : ∀ P : FinitePrime K,
      UpperPrimeFactors (K := K) (L := L) P) :
    IsOpen (ideleBasicSubgroup (K := K) (L := L) T Q :
      Set (FiniteIdeles (OK K) K)) := by
  change IsOpen
    ({a : FiniteIdeles (OK K) K |
      ∀ P, a.1 P ∈ IdeleUnitSubgroup (OK K) K P} ∩
    {a : FiniteIdeles (OK K) K |
      ∀ P, P ∈ T →
        a.1 P ∈
          (finiteCompletionNorm (K := K) (L := L) P (Q P)).range})
  apply IsOpen.inter
  · exact RestrictedProduct.isOpen_forall_mem
      (fun P ↦ idele_unit_open (K := K) P)
  · have hopen : IsOpen (⋂ P ∈ T,
        {a : FiniteIdeles (OK K) K |
          a.1 P ∈
            (finiteCompletionNorm (K := K) (L := L) P (Q P)).range}) := by
      apply isOpen_biInter_finset
      intro P _
      exact (completion_range_open
        (K := K) (L := L) P (Q P)).preimage
          (RestrictedProduct.continuous_eval
            (R := fun P : FinitePrime K ↦ (P.adicCompletion K)ˣ)
            (A := fun P : FinitePrime K ↦
              IdeleUnitSubgroup (OK K) K P)
            (𝓕 := Filter.cofinite) P)
    convert hopen using 1
    ext a
    simp only [Set.mem_iInter, Set.mem_setOf_eq]

set_option synthInstance.maxHeartbeats 300000 in
-- The restricted-product norm range combines all prime-adic topology and
-- local-unit subgroup instances.
set_option maxHeartbeats 3000000 in
-- Assembling openness over every finite prime requires a large dependent
-- restricted-product calculation.
set_option maxRecDepth 100000 in
/-- The image of the finite-idèle norm is open. -/
theorem idele_subgroup_open :
    IsOpen ((finiteIdeleNorm (K := K) (L := L)).range :
      Set (FiniteIdeles (OK K) K)) := by
  classical
  let ramifiedIdeals : Set (Ideal (OK K)) :=
    {p | ∃ q : Ideal (OK L), q.IsPrime ∧ q ≠ ⊥ ∧
      q.under (OK K) = p ∧ Ideal.ramificationIdx p q ≠ 1}
  have hramifiedIdeals : ramifiedIdeals.Finite := by
    exact ramified_base_primes (OK K) (OK L)
  let ramified : Set (FinitePrime K) :=
    {P | P.asIdeal ∈ ramifiedIdeals}
  have hprimeInjective : Function.Injective
      (fun P : FinitePrime K ↦ P.asIdeal) := by
    intro P R h
    exact HeightOneSpectrum.ext_iff.mpr h
  have hramified : ramified.Finite :=
    Set.Finite.preimage hprimeInjective.injOn hramifiedIdeals
  let T : Finset (FinitePrime K) := hramified.toFinset
  let Q : ∀ P : FinitePrime K,
      UpperPrimeFactors (K := K) (L := L) P :=
    fun P ↦ chosenPrimeFactor (K := K) (L := L) P
  apply Subgroup.isOpen_mono
    (H₁ := ideleBasicSubgroup (K := K) (L := L) T Q)
    (H₂ := (finiteIdeleNorm (K := K) (L := L)).range)
    ?_ (idele_basic_open
      (K := K) (L := L) T Q)
  intro a ha
  have hFiniteLift : ∀ P : FinitePrime K,
      ∃ z : ∀ R : FinitePrime L, (R.adicCompletion L)ˣ,
        (∀ R, R.under (OK K) ≠ P → z R = 1) ∧
        (∏ R, finiteCompletionNorm (K := K) (L := L) P R
          (z (upperPrime (K := K) (L := L) P R))) = a.1 P ∧
        (P ∉ T → ∀ R,
          z R ∈ IdeleUnitSubgroup (OK L) L R) := by
    intro P
    by_cases hPT : P ∈ T
    · obtain ⟨z, hzSupport, hzNorm⟩ :=
        lift_completion_range
          (K := K) (L := L) P (Q P) (a.1 P) (ha.2 P hPT)
      exact ⟨z, hzSupport, hzNorm, fun h ↦ (h hPT).elim⟩
    · have hPnotRamified : P ∉ ramified := by
        simpa only [T, Set.Finite.mem_toFinset] using hPT
      have hQunramified : Algebra.IsUnramifiedAt (OK K)
          (upperPrime (K := K) (L := L) P (Q P)).asIdeal := by
        let q := upperPrime (K := K) (L := L) P (Q P)
        letI : q.asIdeal.LiesOver P.asIdeal := by
          constructor
          exact (congrArg HeightOneSpectrum.asIdeal
            (upperPrime_under (K := K) (L := L) P (Q P))).symm
        apply (unramified_ramification_idx
          P.asIdeal q.asIdeal q.ne_bot).2
        by_contra hidx
        apply hPnotRamified
        exact ⟨q.asIdeal, q.isPrime, q.ne_bot,
          congrArg HeightOneSpectrum.asIdeal
            (upperPrime_under (K := K) (L := L) P (Q P)), hidx⟩
      obtain ⟨z, hzSupport, hzUnits, hzNorm⟩ :=
        norm_lift_unramified
          (K := K) (L := L) P (Q P) hQunramified
          (a.1 P) (ha.1 P)
      exact ⟨z, hzSupport, hzNorm, fun _ ↦ hzUnits⟩
  choose zFinite hzFiniteSupport hzFiniteNorm hzFiniteUnits using hFiniteLift
  let upperFinite : ∀ R : FinitePrime L, (R.adicCompletion L)ˣ :=
    fun R ↦ zFinite (R.under (OK K)) R
  let exceptionalSet : Set (FinitePrime L) :=
    {R | R.under (OK K) ∈ T}
  have hexceptionalSet : exceptionalSet.Finite := by
    have hfiber : ∀ P : FinitePrime K,
        Set.Finite {R : FinitePrime L | R.under (OK K) = P} := by
      intro P
      apply Set.Finite.of_finite_image
          (f := fun R : FinitePrime L ↦ R.asIdeal)
      · apply (finite_places (K := K) (L := L) P.asIdeal).subset
        rintro I ⟨R, hR, rfl⟩
        change R.asIdeal ∈ P.asIdeal.primesOver (OK L)
        exact ⟨R.isPrime,
          ⟨(congrArg HeightOneSpectrum.asIdeal hR).symm⟩⟩
      · intro R _ S _ hRS
        exact HeightOneSpectrum.ext hRS
    let U : Set (FinitePrime L) :=
      ⋃ P ∈ (T : Set (FinitePrime K)),
        {R : FinitePrime L | R.under (OK K) = P}
    have hU : U.Finite :=
      T.finite_toSet.biUnion fun P _ ↦ hfiber P
    apply hU.subset
    intro R hR
    apply Set.mem_iUnion.mpr
    refine ⟨R.under (OK K), ?_⟩
    apply Set.mem_iUnion.mpr
    exact ⟨hR, rfl⟩
  let exceptional : Finset (FinitePrime L) :=
    hexceptionalSet.toFinset
  have hFiniteRestricted : ∀ᶠ R in Filter.cofinite,
      upperFinite R ∈ IdeleUnitSubgroup (OK L) L R := by
    rw [Filter.eventually_cofinite]
    refine exceptional.finite_toSet.subset ?_
    intro R hRnotUnit
    by_contra hRexceptional
    apply hRnotUnit
    have hRnotT : R.under (OK K) ∉ T := by
      intro hRT
      apply hRexceptional
      change R ∈ hexceptionalSet.toFinset
      exact (Set.Finite.mem_toFinset hexceptionalSet).2 hRT
    simpa only [upperFinite] using
      hzFiniteUnits (R.under (OK K)) hRnotT R
  let xFinite : FiniteIdeles (OK L) L :=
    RestrictedProduct.mk upperFinite hFiniteRestricted
  refine ⟨xFinite, ?_⟩
  apply RestrictedProduct.ext
  intro P
  change (∏ R : UpperPrimeFactors (K := K) (L := L) P,
    finiteCompletionNorm (K := K) (L := L) P R
      (upperFinite (upperPrime (K := K) (L := L) P R))) = a.1 P
  calc
    _ = ∏ R : UpperPrimeFactors (K := K) (L := L) P,
        finiteCompletionNorm (K := K) (L := L) P R
          (zFinite P (upperPrime (K := K) (L := L) P R)) := by
      apply Finset.prod_congr rfl
      intro R _
      congr 1
      change zFinite
          ((upperPrime (K := K) (L := L) P R).under (OK K))
          (upperPrime (K := K) (L := L) P R) = _
      rw [upperPrime_under]
    _ = a.1 P := hzFiniteNorm P

omit [NumberField K] in
/-- The basic subgroup at an infinite place is open. -/
theorem infinite_basic_open
    (v : InfinitePlace K) :
    IsOpen (infiniteBasicSubgroup (K := K) v :
      Set v.Completionˣ) := by
  classical
  rw [infiniteBasicSubgroup]
  split_ifs with hv
  · change IsOpen ((Units.map
      (InfinitePlace.Completion.ringEquivRealOfIsReal hv).toMonoidHom) ⁻¹'
        (Units.posSubgroup ℝ : Set ℝˣ))
    apply IsOpen.preimage
    · let e : v.Completion ≃ₜ* ℝ :=
        { __ := (InfinitePlace.Completion.ringEquivRealOfIsReal hv).toMulEquiv
          continuous_toFun :=
            (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).continuous
          continuous_invFun :=
            (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous }
      exact (Units.mapContinuousMulEquiv e).continuous
    · rw [show (Units.posSubgroup ℝ : Set ℝˣ) =
          {x : ℝˣ | 0 < (x : ℝ)} by
        ext x
        exact Units.mem_posSubgroup (R := ℝ) x]
      exact isOpen_lt continuous_const Units.continuous_val
  · exact isOpen_univ

private theorem real_unit_pos
    (x : ℝˣ) (hx : 0 < (x : ℝ)) {n : ℕ} (hn : n ≠ 0) :
    ∃ y : ℝˣ, y ^ n = x := by
  let r : ℝ := (x : ℝ) ^ ((n : ℝ)⁻¹)
  have hr : 0 < r := Real.rpow_pos_of_pos hx _
  let y : ℝˣ := Units.mk0 r hr.ne'
  refine ⟨y, ?_⟩
  ext
  exact Real.rpow_inv_natCast_pow hx.le hn

omit [NumberField K] in
/-- Every element of the archimedean basic subgroup has an `n`th root for
positive `n`. -/
theorem pow_infinite_subgroup
    (v : InfinitePlace K) (x : v.Completionˣ)
    (hx : x ∈ infiniteBasicSubgroup (K := K) v)
    (n : ℕ) (hn : 0 < n) :
    ∃ y : v.Completionˣ, y ^ n = x := by
  classical
  by_cases hv : v.IsReal
  · rw [infiniteBasicSubgroup, dif_pos hv] at hx
    let e : v.Completionˣ ≃* ℝˣ :=
      Units.mapEquiv
        (InfinitePlace.Completion.ringEquivRealOfIsReal hv).toMulEquiv
    have hex : 0 < (e x : ℝ) := hx
    obtain ⟨z, hz⟩ := real_unit_pos (e x) hex hn.ne'
    refine ⟨e.symm z, ?_⟩
    apply e.injective
    rw [map_pow, e.apply_symm_apply, hz]
  · rw [infiniteBasicSubgroup, dif_neg hv] at hx
    have hvc : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hv
    let e : v.Completionˣ ≃* ℂˣ :=
      Units.mapEquiv
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hvc).toMulEquiv
    obtain ⟨z, hz⟩ :=
      Submission.CField.KNIndex.complex_monoid_surjective
        n hn (e x)
    refine ⟨e.symm z, ?_⟩
    apply e.injective
    rw [map_pow, e.apply_symm_apply]
    exact hz

/-- Choose one infinite place of `L` above each infinite place of `K`. -/
noncomputable def chosenUpperPlace
    (v : InfinitePlace K) :
    InfinitePlacesAbove (K := K) (L := L) v :=
  ⟨Classical.choose (infinite_place (L := L) v),
    Classical.choose_spec (infinite_place (L := L) v)⟩

set_option synthInstance.maxHeartbeats 300000 in
-- Building a norm lift at the chosen upper infinite place requires resolving
-- the dependent completion extension and norm instances.
set_option maxHeartbeats 2000000 in
-- The explicit lift combines the archimedean root construction with the
-- completion norm formula.
/-- An element of the archimedean basic subgroup has a norm lift supported
at the chosen upper infinite place. -/
theorem infinite_lift_subgroup
    (v : InfinitePlace K) (x : v.Completionˣ)
    (hx : x ∈ infiniteBasicSubgroup (K := K) v) :
    InfiniteNormLift K L v x := by
  classical
  let w := chosenUpperPlace (K := K) (L := L) v
  let F := v.Completion
  let E := w.1.Completion
  letI : Algebra F E :=
    (completionLies v.1 w.1.1
      (infinite_lies_comap v w.1 w.2)).toAlgebra
  letI : Module.Finite F E :=
    infinite_completion_module (K := K) (L := L) v w
  let n := Module.finrank F E
  have hn : 0 < n := Module.finrank_pos
  obtain ⟨r, hr⟩ :=
    pow_infinite_subgroup
      (K := K) v x hx n hn
  let y : Eˣ := Units.map (algebraMap F E) r
  have hy : infiniteCompletionNorm (K := K) (L := L) v w y = x := by
    apply Units.ext
    change Algebra.norm F (algebraMap F E (r : F)) = (x : F)
    rw [Algebra.norm_algebraMap]
    exact congrArg Units.val hr
  let z : ∀ q : InfinitePlace L, q.Completionˣ :=
    Pi.mulSingle
      (M := fun q : InfinitePlace L ↦ q.Completionˣ) w.1 y
  refine ⟨z, ?_, ?_⟩
  · intro q hq
    apply Pi.mulSingle_eq_of_ne
      (M := fun q : InfinitePlace L ↦ q.Completionˣ)
    intro hqw
    apply hq
    rw [hqw, w.2]
  · rw [Finset.prod_eq_single w]
    · change infiniteCompletionNorm (K := K) (L := L) v w (z w.1) = x
      have hzw : z w.1 = y := Pi.mulSingle_eq_same
        (M := fun q : InfinitePlace L ↦ q.Completionˣ) w.1 y
      rw [hzw]
      exact hy
    · intro q _ hq
      have hUpper : q.1 ≠ w.1 := by
        intro h
        apply hq
        exact Subtype.ext h
      change infiniteCompletionNorm (K := K) (L := L) v q (z q.1) = 1
      have hzq : z q.1 = 1 := Pi.mulSingle_eq_of_ne
        (M := fun q : InfinitePlace L ↦ q.Completionˣ) hUpper y
      rw [hzq]
      exact map_one _
    · intro hw
      simp at hw

/-- The product of the archimedean basic subgroups is open. -/
theorem infinite_idele_open :
    IsOpen (infiniteIdeleSubgroup (K := K) :
      Set (InfiniteAdeleRing K)ˣ) := by
  have hopen : IsOpen (⋂ v : InfinitePlace K,
      {a : (InfiniteAdeleRing K)ˣ |
        MulEquiv.piUnits a v ∈ infiniteBasicSubgroup (K := K) v}) := by
    apply isOpen_iInter_of_finite
    intro v
    exact (infinite_basic_open (K := K) v).preimage
      ((continuous_apply v).comp ContinuousMulEquiv.piUnits.continuous)
  convert hopen using 1
  ext a
  change (∀ v, MulEquiv.piUnits a v ∈
    infiniteBasicSubgroup (K := K) v) ↔ _
  simp only [Set.mem_iInter, Set.mem_setOf_eq]

set_option synthInstance.maxHeartbeats 300000 in
-- The infinite-idèle norm uses a dependent product of completion norms and
-- their topological group instances.
set_option maxHeartbeats 2000000 in
-- Openness is assembled from the basic subgroup and coordinatewise norm
-- lifts over all infinite places.
/-- The image of the infinite-idèle norm is open. -/
theorem infinite_subgroup_open :
    IsOpen ((infiniteIdeleNorm (K := K) (L := L)).range :
      Set (InfiniteAdeleRing K)ˣ) := by
  classical
  apply Subgroup.isOpen_mono
    (H₁ := infiniteIdeleSubgroup (K := K))
    (H₂ := (infiniteIdeleNorm (K := K) (L := L)).range)
    ?_ (infinite_idele_open (K := K))
  intro a ha
  have hInfiniteLift : ∀ v : InfinitePlace K,
      InfiniteNormLift K L v (MulEquiv.piUnits a v) := by
    intro v
    exact infinite_lift_subgroup
      (K := K) (L := L) v (MulEquiv.piUnits a v) (ha v)
  choose zInfinite hzInfiniteSupport hzInfiniteNorm using hInfiniteLift
  let upperInfinite : ∀ w : InfinitePlace L, w.Completionˣ :=
    fun w ↦ zInfinite (w.comap (algebraMap K L)) w
  let xInfinite : (InfiniteAdeleRing L)ˣ :=
    MulEquiv.piUnits.symm upperInfinite
  refine ⟨xInfinite, ?_⟩
  apply MulEquiv.piUnits.injective
  funext v
  rw [infinite_idele, infinite_norm]
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
    _ = MulEquiv.piUnits a v := hzInfiniteNorm v

/-- **Proposition V.4.12, global idèle form.**  The image of the idèle norm
for a finite extension of number fields is an open subgroup. -/
theorem idele_norm_open :
    IdeleNormOpen (K := K) (L := L) := by
  let H : Subgroup (IdeleGroup (OK K) K) :=
    ((infiniteIdeleNorm (K := K) (L := L)).range).prod
      ((finiteIdeleNorm (K := K) (L := L)).range)
  apply Subgroup.isOpen_mono
    (H₁ := H) (H₂ := ideleNormSubgroup (K := K) (L := L))
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    refine ⟨(x, y), ?_⟩
    exact Prod.ext hx hy
  · change IsOpen
      (((infiniteIdeleNorm (K := K) (L := L)).range :
          Set (InfiniteAdeleRing K)ˣ) ×ˢ
        ((finiteIdeleNorm (K := K) (L := L)).range :
          Set (FiniteIdeles (OK K) K)))
    exact (infinite_subgroup_open (K := K) (L := L)).prod
      (idele_subgroup_open (K := K) (L := L))

end

end Submission.CField.HNorm
