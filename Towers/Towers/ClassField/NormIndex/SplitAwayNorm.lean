import Towers.NumberTheory.Galois.PlaceCompletionDegree
import Towers.NumberTheory.Galois.CompositumSplittingPrimes
import Towers.ClassField.NormIndex.CompletionPlaceComparison
import Towers.ClassField.NormIndex.PlaceIndex

/-!
# The split-away norm input for Proposition VII.4.6

This file constructs the remaining norm input in the proof of Proposition
VII.4.6.  The first step below records the key local fact: at a completely
split finite prime, every completed local norm is surjective.
-/

namespace Towers.CField.NIndex

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo
open scoped Pointwise

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

private abbrev IK (K : Type u) [Field K] [NumberField K] :=
  IdeleGroup (NumberField.RingOfIntegers K) K

private noncomputable def chosenUpperFactor
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (OK K)) :
    UpperPrimeFactors (K := K) (L := L) P := by
  letI : Fact (FinitePlace.mk P).val.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist (FinitePlace.mk P).val.Completion :=
    placeUltrametricDist P
  exact placeUpperFactor (K := K) (L := L) P
    (Classical.choice (absolute_value_extension
      (K := K) (L := L) (FinitePlace.mk P).val))

private noncomputable def chosenUpperPrime
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (OK K)) : HeightOneSpectrum (OK L) :=
  upperPrime (K := K) (L := L) P
    (chosenUpperFactor (K := K) (L := L) P)

private theorem upper_prime_chosen
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (OK K))
    (Q : UpperPrimeFactors (K := K) (L := L) P) :
    upperPrime (K := K) (L := L) P Q =
        chosenUpperPrime (K := K) (L := L)
          ((upperPrime (K := K) (L := L) P Q).under (OK K)) ↔
      Q = chosenUpperFactor (K := K) (L := L) P := by
  rw [upperPrime_under]
  constructor
  · intro h
    apply upper_base_injective (K := K) (L := L) P
    apply Subtype.ext
    exact h
  · rintro rfl
    rfl

set_option maxHeartbeats 3000000 in
-- Comparing the dependent absolute and adic completion models is expensive.
set_option maxRecDepth 100000 in
/-- At a completely split finite prime, every completed upper factor has
degree one over the base completion. -/
theorem finrank_splits_completely
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (OK K))
    (Q : UpperPrimeFactors (K := K) (L := L) P)
    (hsplit : SplitsCompletelyAt K L P) :
    let hP : P.asIdeal.map (algebraMap (OK K) (OK L)) ≠ ⊥ :=
      Ideal.map_ne_bot_of_ne_bot P.ne_bot
    letI : Algebra (P.adicCompletion K)
        ((upperPrime (K := K) (L := L) P Q).adicCompletion L) :=
      adicFactorAlgebra (K := K) (L := L) P hP Q
    Module.finrank (P.adicCompletion K)
      ((upperPrime (K := K) (L := L) P Q).adicCompletion L) = 1 := by
  let v := (FinitePlace.mk P).val
  let w : CompletionPlacesAbove (L := L) v :=
    (placesAboveFactors
      (K := K) (L := L) P).symm Q
  let Qw := placeUpperFactor
    (K := K) (L := L) P w
  have hQ : Qw = Q :=
    place_upper_symm
      (K := K) (L := L) P Q
  rw [← hQ]
  let q := upperPrime (K := K) (L := L) P Qw
  let eK := placeCompletionAdic P
  let eL := completionPlaceAdic (K := K) (L := L) P w
  let hP : P.asIdeal.map (algebraMap (OK K) (OK L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot P.ne_bot
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : Algebra (P.adicCompletion K) (q.adicCompletion L) :=
    adicFactorAlgebra (K := K) (L := L) P hP Qw
  letI : FiniteDimensional (P.adicCompletion K) (q.adicCompletion L) :=
    finite_completion_module (K := K) (L := L) P Qw
  letI : MulSemiringAction Gal(L/K) (OK L) :=
    IsIntegralClosure.MulSemiringAction (OK K) K L (OK L)
  letI : SMulCommClass Gal(L/K) (OK K) (OK L) :=
    { smul_comm := fun sigma a b => by
        apply Subtype.ext
        have hG (x : OK L) : ((sigma • x : OK L) : L) = sigma (x : L) :=
          algebraMap.coe_smul' (B := OK L) (C := L) sigma x
        have hA (x : OK L) : ((a • x : OK L) : L) =
            (a : K) • (x : L) :=
          algebraMap.coe_smul (A := OK K) (B := OK L) (C := L) a x
        calc
          ((sigma • (a • b) : OK L) : L) =
              sigma (((a • b : OK L) : L)) := hG (a • b)
          _ = sigma ((a : K) • (b : L)) := congrArg sigma (hA b)
          _ = (a : K) • sigma (b : L) := smul_comm sigma (a : K) (b : L)
          _ = (a : K) • ((sigma • b : OK L) : L) :=
            congrArg (fun y : L ↦ (a : K) • y) (hG b).symm
          _ = ((a • (sigma • b) : OK L) : L) := (hA (sigma • b)).symm }
  letI : Algebra.IsInvariant (OK K) (OK L) Gal(L/K) :=
    Algebra.isInvariant_of_isGalois (A := OK K) (K := K)
      (L := L) (B := OK L)
  letI : IsGaloisGroup Gal(L/K) (OK K) (OK L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) (OK K) (OK L) K L
  have hcenter : nonarchimedeanHeightSpectrum w.1
      (absolute_extension_nontrivial v w)
      (absolute_extension_nonarchimedean v w) = q := by
    calc
      nonarchimedeanHeightSpectrum w.1
          (absolute_extension_nontrivial v w)
          (absolute_extension_nonarchimedean v w) =
          (placeAboveBase
            (K := K) (L := L) P w).1 := rfl
      _ = upperPrime (K := K) (L := L) P
          (placeUpperFactor
            (K := K) (L := L) P w) :=
        (upper_place_factor
          (K := K) (L := L) P w).symm
      _ = q := by
        rfl
  have hqmem : q.asIdeal ∈ Ideal.primesOver P.asIdeal (OK L) := by
    refine ⟨q.isPrime, ⟨?_⟩⟩
    exact congrArg HeightOneSpectrum.asIdeal
      (upperPrime_under (K := K) (L := L) P Qw) |>.symm
  have hstab : MulAction.stabilizer Gal(L/K) q.asIdeal = ⊥ :=
    (splits_completely_bot P q.asIdeal hqmem).mp hsplit
  have hdecomp : absoluteValueDecomposition v w.1 = ⊥ := by
    rw [← centered_stabilizer_decomposition v w.1
      (absolute_extension_nontrivial v w)
      (absolute_extension_nonarchimedean v w), hcenter]
    exact hstab
  have habs : Module.finrank v.Completion w.1.Completion = 1 := by
    rw [finrank_decomposition_card P w,
      hdecomp]
    simp
  have hcomp :
      (algebraMap (P.adicCompletion K) (q.adicCompletion L)).comp
          eK.toRingHom =
        eL.toRingHom.comp (algebraMap v.Completion w.1.Completion) := by
    exact place_adic_algebra
      (K := K) (L := L) P w
  have hadic : Module.finrank (P.adicCompletion K) (q.adicCompletion L) = 1 := by
    rw [← habs]
    exact (Algebra.finrank_eq_of_equiv_equiv eK eL hcomp).symm
  exact hadic

set_option maxHeartbeats 1000000 in
-- Normalizing the dependent completion algebra structures is expensive.
set_option maxRecDepth 100000 in
/-- The scalar embedding is a canonical section of a completed norm at a
completely split finite prime. -/
theorem extension_splits_completely
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (OK K))
    (Q : UpperPrimeFactors (K := K) (L := L) P)
    (hsplit : SplitsCompletelyAt K L P) (y : (P.adicCompletion K)ˣ) :
    finiteCompletionNorm (K := K) (L := L) P Q
        (factorMonoidHom (K := K) (L := L) P Q y) = y := by
  let hP : P.asIdeal.map (algebraMap (OK K) (OK L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot P.ne_bot
  let q := upperPrime (K := K) (L := L) P Q
  letI : Algebra (P.adicCompletion K) (q.adicCompletion L) :=
    adicFactorAlgebra (K := K) (L := L) P hP Q
  letI : FiniteDimensional (P.adicCompletion K) (q.adicCompletion L) :=
    finite_completion_module (K := K) (L := L) P Q
  apply Units.ext
  change Algebra.norm (P.adicCompletion K)
      (algebraMap (P.adicCompletion K) (q.adicCompletion L)
        (y : P.adicCompletion K)) = (y : P.adicCompletion K)
  rw [Algebra.norm_algebraMap,
    finrank_splits_completely P Q hsplit, pow_one]

/-- At a completely split finite prime, the norm from each completed upper
factor is onto the multiplicative group of the base completion. -/
theorem surjective_splits_completely
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (OK K))
    (Q : UpperPrimeFactors (K := K) (L := L) P)
    (hsplit : SplitsCompletelyAt K L P) :
    Function.Surjective (finiteCompletionNorm (K := K) (L := L) P Q) := by
  intro y
  refine ⟨factorMonoidHom (K := K) (L := L) P Q y, ?_⟩
  exact extension_splits_completely
    P Q hsplit y

private theorem idele_unit_cast
    {L : Type u} [Field L] [NumberField L]
    {R R' : HeightOneSpectrum (OK L)} (h : R = R')
    (x : (R.adicCompletion L)ˣ)
    (hx : x ∈ IdeleUnitSubgroup (OK L) L R) :
    Units.map ((RingEquiv.cast
      (R := fun V : HeightOneSpectrum (OK L) ↦ V.adicCompletion L)
      h).toRingHom.toMonoidHom) x ∈
        IdeleUnitSubgroup (OK L) L R' := by
  subst R'
  exact hx

private theorem units_cast_comp
    {I J : Type*} (f : I → J) {R : J → Type*}
    [∀ j, Semiring (R j)] (x : ∀ i, (R (f i))ˣ)
    {i i' : I} (h : i = i') :
    Units.map ((RingEquiv.cast (R := R) (congrArg f h)).toRingHom.toMonoidHom)
        (x i) = x i' := by
  subst i'
  rfl

private noncomputable def splitFiniteCoordinate
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (HeightOneSpectrum (OK K)))
    (a : FiniteIdeles (OK K) K)
    (R : HeightOneSpectrum (OK L)) : (R.adicCompletion L)ˣ := by
  let P := R.under (OK K)
  if hP : P ∈ S then
    exact 1
  else
    let Q := chosenUpperFactor (K := K) (L := L) P
    let R₀ := chosenUpperPrime (K := K) (L := L) P
    if hR : R = R₀ then
      exact Units.map ((RingEquiv.cast
        (R := fun V : HeightOneSpectrum (OK L) ↦ V.adicCompletion L)
        hR.symm).toRingHom.toMonoidHom)
          (factorMonoidHom (K := K) (L := L) P Q (a.1 P))
    else
      exact 1

private noncomputable def splitFinitePreimage
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (HeightOneSpectrum (OK K)))
    (a : FiniteIdeles (OK K) K) : FiniteIdeles (OK L) L := by
  refine ⟨splitFiniteCoordinate (K := K) (L := L) S a, ?_⟩
  have ha : ∀ᶠ P in Filter.cofinite,
      a.1 P ∈ IdeleUnitSubgroup (OK K) K P := a.property
  have ha' : ∀ᶠ R : HeightOneSpectrum (OK L) in Filter.cofinite,
      a.1 (R.under (OK K)) ∈
        IdeleUnitSubgroup (OK K) K (R.under (OK K)) :=
    (prime_cofinite (K := K) (L := L)) ha
  filter_upwards [ha'] with R hR
  dsimp only [splitFiniteCoordinate]
  by_cases hP : R.under (OK K) ∈ S
  · simp only [hP, dite_true]
    exact (IdeleUnitSubgroup (OK L) L R).one_mem
  · simp only [hP, dite_false]
    by_cases hchosen : R = chosenUpperPrime
        (K := K) (L := L) (R.under (OK K))
    · rw [dif_pos hchosen]
      apply idele_unit_cast hchosen.symm
      apply factor_extension_preserves
      exact hR
    · rw [dif_neg hchosen]
      exact (IdeleUnitSubgroup (OK L) L R).one_mem

set_option maxHeartbeats 2000000 in
-- The selected restricted-product coordinate carries several dependent casts.
set_option maxRecDepth 100000 in
/-- The selected one-factor restricted-product section maps to the prescribed
finite idèle when the coordinates in `S` are one and every prime outside `S`
splits completely. -/
theorem idele_split_preimage
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (HeightOneSpectrum (OK K)))
    (a : FiniteIdeles (OK K) K)
    (haS : ∀ P ∈ S, a.1 P = 1)
    (hsplit : ∀ P, P ∉ S → SplitsCompletelyAt K L P) :
    finiteIdeleNorm (K := K) (L := L)
        (splitFinitePreimage (K := K) (L := L) S a) = a := by
  classical
  apply RestrictedProduct.ext
  intro P
  change (∏ Q : UpperPrimeFactors (K := K) (L := L) P,
      finiteCompletionNorm (K := K) (L := L) P Q
        ((splitFinitePreimage (K := K) (L := L) S a).1
          (upperPrime (K := K) (L := L) P Q))) = a.1 P
  by_cases hP : P ∈ S
  · rw [haS P hP]
    apply Finset.prod_eq_one
    intro Q _
    change finiteCompletionNorm (K := K) (L := L) P Q
      (splitFiniteCoordinate (K := K) (L := L) S a
        (upperPrime (K := K) (L := L) P Q)) = 1
    dsimp only [splitFiniteCoordinate]
    simp only [upperPrime_under]
    simp only [hP, dite_true, map_one]
  · let Q₀ := chosenUpperFactor (K := K) (L := L) P
    rw [Finset.prod_eq_single Q₀]
    · change finiteCompletionNorm (K := K) (L := L) P Q₀
        (splitFiniteCoordinate (K := K) (L := L) S a
          (upperPrime (K := K) (L := L) P Q₀)) = a.1 P
      rw [show splitFiniteCoordinate (K := K) (L := L) S a
          (upperPrime (K := K) (L := L) P Q₀) =
            factorMonoidHom (K := K) (L := L) P Q₀ (a.1 P) by
        dsimp only [splitFiniteCoordinate]
        have hunder :
            (upperPrime (K := K) (L := L) P Q₀).under (OK K) = P :=
          upperPrime_under (K := K) (L := L) P Q₀
        have hP' :
            (upperPrime (K := K) (L := L) P Q₀).under (OK K) ∉ S := by
          simpa only [hunder] using hP
        rw [dif_neg hP']
        have hchosen : upperPrime (K := K) (L := L) P Q₀ =
            chosenUpperPrime (K := K) (L := L)
              ((upperPrime (K := K) (L := L) P Q₀).under (OK K)) := by
          rw [hunder]
          rfl
        rw [dif_pos hchosen]
        let x : ∀ T : HeightOneSpectrum (OK K),
            ((chosenUpperPrime (K := K) (L := L) T).adicCompletion L)ˣ :=
          fun T ↦ factorMonoidHom (K := K) (L := L) T
            (chosenUpperFactor (K := K) (L := L) T) (a.1 T)
        have hx := units_cast_comp
          (fun T : HeightOneSpectrum (OK K) ↦
            chosenUpperPrime (K := K) (L := L) T)
          (R := fun V : HeightOneSpectrum (OK L) ↦ V.adicCompletion L)
          x hunder
        exact hx]
      exact extension_splits_completely
        P Q₀ (hsplit P hP) (a.1 P)
    · intro Q _ hQ
      change finiteCompletionNorm (K := K) (L := L) P Q
        (splitFiniteCoordinate (K := K) (L := L) S a
          (upperPrime (K := K) (L := L) P Q)) = 1
      dsimp only [splitFiniteCoordinate]
      simp only [upperPrime_under]
      simp only [hP, dite_false]
      have hnot : upperPrime (K := K) (L := L) P Q ≠
          chosenUpperPrime (K := K) (L := L) P := by
        intro heq
        apply hQ
        apply upper_base_injective (K := K) (L := L) P
        apply Subtype.ext
        exact heq
      rw [dif_neg hnot, map_one]
    · intro hQ₀
      exact (hQ₀ (Finset.mem_univ Q₀)).elim

private noncomputable def splitIdelePreimage
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (HeightOneSpectrum (OK K)))
    (a : IdeleGroup (OK K) K) : IdeleGroup (OK L) L :=
  (1, splitFinitePreimage (K := K) (L := L) S a.2)

set_option maxHeartbeats 3000000 in
-- The finite component unfolds the dependent restricted-product section.
set_option maxRecDepth 100000 in
/-- The split-away section is a right inverse to the full idèle norm on
idèles which are one at `S` and at every infinite place. -/
theorem norm_split_preimage
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (HeightOneSpectrum (OK K)))
    (a : IdeleGroup (OK K) K) (ha : a ∈ IdelesAwayFrom K S)
    (hsplit : ∀ P, P ∉ S → SplitsCompletelyAt K L P) :
    ideleNorm (K := K) (L := L)
        (splitIdelePreimage (K := K) (L := L) S a) = a := by
  apply Prod.ext
  · change infiniteIdeleNorm (K := K) (L := L) 1 = a.1
    rw [map_one]
    apply MulEquiv.piUnits.injective
    funext w
    have haw := ha.2 w
    change MulEquiv.piUnits a.1 w = 1 at haw
    rw [haw]
    exact congrFun (map_one (MulEquiv.piUnits :
      (InfiniteAdeleRing K)ˣ ≃* ((w : InfinitePlace K) → w.Completionˣ))) w
  · exact idele_split_preimage
      S a.2 ha.1 hsplit

/-- Completely split finite places outside `S` supply a restricted-product
preimage for every idèle in `I^S`. -/
theorem splitAwayBridge :
    SplitAwayBridge.{u} := by
  intro K L _ _ _ _ _ _ _ S hsplit a ha
  exact ⟨splitIdelePreimage (K := K) (L := L) S a,
    norm_split_preimage S a ha hsplit⟩

/-- With split-away norm assembly now internal, Proposition VII.4.6 depends
only on Lemma VII.4.5. -/
theorem split_away_only
    (h45 : (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsSolvable Gal(L/K)],
          ∀ D : Subgroup (IK K),
            D ≤ ideleNormSubgroup (K := K) (L := L) →
            Dense ((principalIdeles (NumberField.RingOfIntegers K) K ⊔ D :
              Subgroup (IK K)) : Set (IK K)) →
            Module.finrank K L = 1)) :
    NontrivialNonsplitPrimes.{u} :=
  place_statement_away h45
    splitAwayBridge

end

end Towers.CField.NIndex
