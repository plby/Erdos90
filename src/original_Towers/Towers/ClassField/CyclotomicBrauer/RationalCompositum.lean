import Towers.ClassField.CyclotomicBrauer.CyclotomicCompositum
import Towers.ClassField.CyclotomicBrauer.TotallyComplex
import Towers.ClassField.CyclotomicBrauer.CompletionEquiv

/-!
# Lemma VII.7.3: rational prime-power compositum

This file instantiates the common-ambient compositum machinery for a finite
family of rational prime-power blocks.  It retains the prime labelling used
to prove pairwise coprimality of the actual global degrees.
-/

namespace Towers.CField.CBrauer

open AbsoluteValue IntermediateField IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo

noncomputable section

universe u

/-- A homogeneous wrapper around prime-power blocks with varying primes and
exponents. -/
structure RationalCompositumFactor
    (S : Finset (finitePrime ℚ)) where
  prime : ℕ
  exponent : ℕ
  prime_isPrime : prime.Prime
  block : RationalPrimeBlock S prime exponent

/-- Odd prime divisors of `N`, together with one distinguished two-primary
slot.  The latter is present even when `N` is odd, because a totally complex
number field must have even degree. -/
abbrev RationalCompositumIndex (N : ℕ) :=
  Sum {ell : N.primeFactors // (ell : ℕ) ≠ 2} Unit

set_option synthInstance.maxHeartbeats 200000 in
-- The chosen family carries dependent field, algebra, and compositum tower instances.
set_option maxHeartbeats 2000000 in
/-- A finite family of prime-power blocks labelled injectively by primes has
a cyclic cyclotomic compositum over `ℚ`.  This theorem performs all choices
of compatible cyclotomic-overfield embeddings into `AlgebraicClosure ℚ`.
Local-degree and total-complexity assertions are retained for the sharper
prime-factor instantiation below. -/
theorem rational_cyclic_compositum
    {I : Type*} [Fintype I]
    (S : Finset (finitePrime ℚ))
    (factors : I → RationalCompositumFactor S)
    (hprimeInjective : Function.Injective fun i ↦ (factors i).prime)
    (complexIndex : I)
    (hcomplex : (factors complexIndex).block.extension.IsTotallyComplex) :
    ∃ data : FEData ℚ,
      data.IsCyclicCyclotomic ∧ data.IsTotallyComplex ∧
        data.LocalDegreesDvd S
          (∏ i, (factors i).prime ^ (factors i).exponent) := by
  let Omega := AlgebraicClosure ℚ
  choose blockFields cyclotomicFields embedded using fun i ↦
    embedded_cyclic_data
      (factors i).block.extension
      (factors i).block.isCyclicCyclotomic Omega
  letI (i : I) : Algebra ℚ (blockFields i) := (blockFields i).algebra'
  letI (i : I) : Algebra ℚ (cyclotomicFields i) :=
    (cyclotomicFields i).algebra'
  have hle : ∀ i, blockFields i ≤ cyclotomicFields i := fun i ↦
    (embedded i).2.1
  letI (i : I) : FiniteDimensional ℚ (blockFields i) :=
    (embedded i).2.2.1
  letI (i : I) : IsGalois ℚ (blockFields i) :=
    (embedded i).2.2.2.1
  letI (i : I) : IsCyclic Gal(↑(blockFields i)/ℚ) :=
    (embedded i).2.2.2.2.1
  letI (i : I) : Field (factors i).block.extension.L :=
    (factors i).block.extension.fieldL
  letI (i : I) : NumberField (factors i).block.extension.L :=
    (factors i).block.extension.numberFieldL
  letI (i : I) : Algebra ℚ (factors i).block.extension.L :=
    (factors i).block.extension.algebraKL
  letI (i : I) : FiniteDimensional ℚ (factors i).block.extension.L :=
    (factors i).block.extension.finiteDimensionalKL
  letI (i : I) : IsGalois ℚ (factors i).block.extension.L :=
    (factors i).block.extension.isGaloisKL
  choose conductors hcyclotomic using fun i ↦
    (embedded i).2.2.2.2.2
  choose degreeExponents hdegree using fun i ↦
    (factors i).block.degree_prime_power
  have hdegreeEmbedded : ∀ i,
      Module.finrank ℚ ↑(blockFields i) =
        (factors i).prime ^ degreeExponents i := by
    intro i
    let blockEquiv := Classical.choice (embedded i).1
    calc
      Module.finrank ℚ ↑(blockFields i) =
          Module.finrank ℚ (factors i).block.extension.L :=
        blockEquiv.symm.toLinearEquiv.finrank_eq
      _ = (factors i).prime ^ degreeExponents i := hdegree i
  have hcoprime : Set.Pairwise (Set.univ : Set I)
      (Function.onFun Nat.Coprime fun i ↦
        Module.finrank ℚ ↑(blockFields i)) := by
    intro i _ j _ hij
    change Nat.Coprime (Module.finrank ℚ ↑(blockFields i))
      (Module.finrank ℚ ↑(blockFields j))
    rw [hdegreeEmbedded i, hdegreeEmbedded j]
    apply Nat.coprime_pow_primes _ _
      (factors i).prime_isPrime (factors j).prime_isPrime
    intro hprime
    exact hij (hprimeInjective hprime)
  have hcoprimeTargets : Set.Pairwise (Set.univ : Set I)
      (Function.onFun Nat.Coprime fun i ↦
        (factors i).prime ^ (factors i).exponent) := by
    intro i _ j _ hij
    exact Nat.coprime_pow_primes _ _
      (factors i).prime_isPrime (factors j).prime_isPrime
      (fun hprime ↦ hij (hprimeInjective hprime))
  choose originalPlaces originalDegrees using fun i ↦
    (factors i).block.hasLocalDegrees
  obtain ⟨compositum, cyclotomicOverfield, hblocksLe, hleOverfield,
      finiteCompositum, galoisCompositum, cyclicCompositum, _hdegreeCompositum,
      conductor, cyclotomicOverfield_isCyclotomic⟩ :=
    cyclic_cyclotomic_compositum
      blockFields cyclotomicFields conductors hcyclotomic Finset.univ
      (fun i _ ↦ hle i) (by
        simpa only [Finset.coe_univ] using hcoprime)
  letI : Algebra ℚ compositum := compositum.algebra'
  letI : FiniteDimensional ℚ compositum := finiteCompositum
  letI : IsGalois ℚ compositum := galoisCompositum
  letI : NumberField compositum := NumberField.of_module_finite ℚ compositum
  letI : IsCyclic Gal(↑compositum/ℚ) := cyclicCompositum
  letI : Algebra ℚ cyclotomicOverfield := cyclotomicOverfield.algebra'
  letI : IsCyclotomicExtension {conductor} ℚ cyclotomicOverfield :=
    cyclotomicOverfield_isCyclotomic
  letI : NumberField cyclotomicOverfield :=
    IsCyclotomicExtension.numberField {conductor} ℚ cyclotomicOverfield
  letI : Algebra compositum cyclotomicOverfield :=
    (IntermediateField.inclusion hleOverfield).toRingHom.toAlgebra
  letI : IsScalarTower ℚ compositum cyclotomicOverfield := by
    apply IsScalarTower.of_algebraMap_eq'
    rfl
  let complexBlockField := blockFields complexIndex
  letI : NumberField complexBlockField :=
    NumberField.of_module_finite ℚ complexBlockField
  let complexBlockEquiv := Classical.choice (embedded complexIndex).1
  letI : Algebra (factors complexIndex).block.extension.L complexBlockField :=
    complexBlockEquiv.toRingHom.toAlgebra
  letI : NumberField.IsTotallyComplex
      (factors complexIndex).block.extension.L := hcomplex
  letI : NumberField.IsTotallyComplex complexBlockField :=
    NumberField.isTotallyComplex_of_algebra
      (factors complexIndex).block.extension.L complexBlockField
  have hcomplexBlockLe : complexBlockField ≤ compositum := by
    simpa only [complexBlockField] using
      hblocksLe complexIndex (Finset.mem_univ complexIndex)
  letI : Algebra complexBlockField compositum :=
    (IntermediateField.inclusion hcomplexBlockLe).toRingHom.toAlgebra
  have htotallyComplexCompositum : NumberField.IsTotallyComplex compositum :=
    NumberField.isTotallyComplex_of_algebra complexBlockField compositum
  let finalPlaces : ∀ P : S,
      CompletionPlacesAbove (L := compositum) (FinitePlace.mk P.1).val :=
    fun P ↦ by
      let v := (FinitePlace.mk P.1).val
      letI : Fact v.IsNontrivial :=
        ⟨absolute_value_nontrivial P.1⟩
      letI : IsUltrametricDist v.Completion :=
        placeUltrametricDist P.1
      exact Classical.choice
        (absolute_value_extension (K := ℚ) (L := compositum) v)
  have hlocalDegrees :
      let data : FEData ℚ :=
        { L := compositum
          fieldL := inferInstance
          numberFieldL := inferInstance
          algebraKL := inferInstance
          finiteDimensionalKL := inferInstance
          isGaloisKL := inferInstance }
      data.LocalDegreesDvd S
        (∏ i, (factors i).prime ^ (factors i).exponent) := by
    dsimp only [FEData.LocalDegreesDvd]
    refine ⟨finalPlaces, ?_⟩
    intro P
    let v := (FinitePlace.mk P.1).val
    let w := finalPlaces P
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P.1⟩
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist P.1
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    have hfactorDvd : ∀ i : I,
        (factors i).prime ^ (factors i).exponent ∣
          Module.finrank v.Completion w.1.Completion := by
      intro i
      let blockField := blockFields i
      letI : NumberField blockField :=
        NumberField.of_module_finite ℚ blockField
      have hblockLe : blockField ≤ compositum :=
        hblocksLe i (Finset.mem_univ i)
      letI : Algebra blockField compositum :=
        (IntermediateField.inclusion hblockLe).toRingHom.toAlgebra
      letI : IsScalarTower ℚ blockField compositum := by
        apply IsScalarTower.of_algebraMap_eq'
        rfl
      letI : FiniteDimensional blockField compositum :=
        FiniteDimensional.right ℚ blockField compositum
      letI : IsGalois blockField compositum :=
        IsGalois.tower_top_of_isGalois ℚ blockField compositum
      let u : AbsoluteValue blockField ℝ :=
        w.1.comp (algebraMap blockField compositum).injective
      let huv : AbsoluteValue.LiesOver u v := by
        constructor
        ext x
        calc
          w.1 (algebraMap blockField compositum
              (algebraMap ℚ blockField x)) =
              w.1 (algebraMap ℚ compositum x) := by
            rw [IsScalarTower.algebraMap_apply ℚ blockField compositum]
          _ = v x := DFunLike.congr_fun w.2.comp_eq x
      let hwu : AbsoluteValue.LiesOver w.1 u := ⟨rfl⟩
      let blockEquiv := Classical.choice (embedded i).1
      let originalPlace : AbsoluteValue (factors i).block.extension.L ℝ :=
        pullbackAbsoluteValue blockEquiv u
      let horiginalv : AbsoluteValue.LiesOver originalPlace v :=
        pullback_absolute_lies blockEquiv v u huv
      let originalAbove : CompletionPlacesAbove
          (L := (factors i).block.extension.L) v :=
        ⟨originalPlace, horiginalv⟩
      let selectedAbove := originalPlaces i P
      letI : Algebra v.Completion originalPlace.Completion :=
        (completionLies v originalPlace horiginalv).toAlgebra
      letI : Algebra v.Completion selectedAbove.1.Completion :=
        (completionLies v selectedAbove.1 selectedAbove.2).toAlgebra
      letI : Algebra v.Completion u.Completion :=
        (completionLies v u huv).toAlgebra
      letI : Algebra u.Completion w.1.Completion :=
        (completionLies u w.1 hwu).toAlgebra
      have hselectedEq : Module.finrank v.Completion originalPlace.Completion =
          Module.finrank v.Completion selectedAbove.1.Completion :=
        place_completion_finrank P.1 originalAbove selectedAbove
      have hembeddedEq : Module.finrank v.Completion originalPlace.Completion =
          Module.finrank v.Completion u.Completion :=
        by
          simpa only [originalPlace] using
            completion_finrank_alg blockEquiv v u huv
      have htargetEmbedded :
          (factors i).prime ^ (factors i).exponent ∣
            Module.finrank v.Completion u.Completion := by
        have htargetSelected :
            (factors i).prime ^ (factors i).exponent ∣
              Module.finrank v.Completion selectedAbove.1.Completion := by
          simpa only [v, selectedAbove] using originalDegrees i P
        rw [← hselectedEq, hembeddedEq] at htargetSelected
        exact htargetSelected
      have hembeddedFinal : Module.finrank v.Completion u.Completion ∣
          Module.finrank v.Completion w.1.Completion :=
        finrank_dvd_tower blockField v u w.1
          huv hwu w.2
      exact htargetEmbedded.trans hembeddedFinal
    apply dvd_pairwise_coprime Finset.univ
      (fun i ↦ (factors i).prime ^ (factors i).exponent)
      (Module.finrank v.Completion w.1.Completion)
    · simpa only [Finset.coe_univ] using hcoprimeTargets
    · intro i _
      exact hfactorDvd i
  let data : FEData ℚ :=
    { L := compositum
      fieldL := inferInstance
      numberFieldL := inferInstance
      algebraKL := inferInstance
      finiteDimensionalKL := inferInstance
      isGaloisKL := inferInstance }
  refine ⟨data, ?_, htotallyComplexCompositum, ?_⟩
  · change IsCyclic Gal(↑compositum/ℚ) ∧ _
    exact ⟨inferInstance, conductor, cyclotomicOverfield, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, trivial⟩
  · exact hlocalDegrees

/-- Instantiate the abstract finite-family theorem with all odd prime
factors of `N` and the distinguished totally complex two-primary block. -/
theorem rational_cyclotomic_compositum
    (S : Finset (finitePrime ℚ)) (N : ℕ) (hN : N ≠ 0)
    (blocks : ∀ ell : N.primeFactors,
      RationalPrimeBlock
        S ell.1 (N.factorization ell.1)) :
    ∃ data : FEData ℚ,
      data.IsCyclicCyclotomic ∧ data.IsTotallyComplex ∧
        data.LocalDegreesDvd S N := by
  let twoBlock := Classical.choice
    (complex_two_block S (N.factorization 2))
  let factors : RationalCompositumIndex N →
      RationalCompositumFactor S
    | Sum.inl ell =>
        { prime := ell.1.1
          exponent := N.factorization ell.1.1
          prime_isPrime := Nat.prime_of_mem_primeFactors ell.1.2
          block := blocks ell.1 }
    | Sum.inr _ =>
        { prime := 2
          exponent := max 1 (N.factorization 2)
          prime_isPrime := Nat.prime_two
          block := twoBlock.1 }
  have hprimeInjective : Function.Injective fun i ↦ (factors i).prime := by
    intro i j hij
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            exact congrArg Sum.inl (Subtype.ext (Subtype.ext hij))
        | inr j =>
            exfalso
            exact i.2 hij
    | inr i =>
        cases j with
        | inl j =>
            exfalso
            exact j.2 hij.symm
        | inr j =>
            exact congrArg Sum.inr (Subsingleton.elim i j)
  obtain ⟨data, hcyclic, hcomplex, hlocalProduct⟩ :=
    rational_cyclic_compositum
      S factors hprimeInjective (Sum.inr ()) twoBlock.2
  have hNdivProduct : N ∣
      ∏ i : RationalCompositumIndex N,
        (factors i).prime ^ (factors i).exponent := by
    apply dvd_prime_targets N _ hN
    intro ell
    by_cases hell2 : (ell : ℕ) = 2
    · have hpow : 2 ^ N.factorization 2 ∣
          2 ^ max 1 (N.factorization 2) :=
        pow_dvd_pow 2 (le_max_right 1 (N.factorization 2))
      have hfactor : 2 ^ max 1 (N.factorization 2) ∣
          ∏ i : RationalCompositumIndex N,
            (factors i).prime ^ (factors i).exponent := by
        simpa only [factors] using
          (Finset.dvd_prod_of_mem
            (fun i : RationalCompositumIndex N ↦
              (factors i).prime ^ (factors i).exponent)
            (Finset.mem_univ (Sum.inr ())))
      simpa only [hell2] using hpow.trans hfactor
    · let index : RationalCompositumIndex N :=
        Sum.inl ⟨ell, hell2⟩
      have hfactor : (factors index).prime ^ (factors index).exponent ∣
          ∏ i : RationalCompositumIndex N,
            (factors i).prime ^ (factors i).exponent :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ index)
      simpa only [index, factors] using hfactor
  refine ⟨data, hcyclic, hcomplex, ?_⟩
  rcases hlocalProduct with ⟨places, hdegrees⟩
  exact ⟨places, fun P ↦ hNdivProduct.trans (hdegrees P)⟩

/-- The rational cyclic-compositum bridge in Lemma VII.7.3 is
unconditional. -/
theorem rationalCompositumBridge :
    RationalCompositumBridge := by
  intro S N hN blocks
  exact rational_cyclotomic_compositum
    S N hN blocks

/-- After the rational compositum is discharged, rational-to-number-field
base change is the sole remaining input to Lemma VII.7.3. -/
theorem rational_compositum_change
    (hbaseChange : ChangeRationalsBridge.{u}) :
    (∀ (K : Type u) [Field K] [NumberField K]
          (S : Finset (finitePrime K)) (m : ℕ),
          0 < m →
            ∃ data : FEData K,
              data.IsCyclicCyclotomic ∧
                data.IsTotallyComplex ∧
                data.LocalDegreesDvd S m) :=
  blocks_compositum_change
    rationalCompositumBridge hbaseChange

/-- The exact one-input boundary consumed by Proposition VII.7.2. -/
theorem rationalCompositum
    (hbaseChange : ChangeRationalsBridge.{u}) :
    FinitePrime.{u} :=
  primePowerBlocks
    rationalCompositumBridge hbaseChange

end

end Towers.CField.CBrauer
