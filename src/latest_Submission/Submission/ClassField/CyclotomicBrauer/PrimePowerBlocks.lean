import Submission.ClassField.CyclotomicBrauer.CyclotomicLocalDegree
import Submission.ClassField.CyclotomicBrauer.OddPowerField
import Submission.ClassField.CyclotomicBrauer.TwoPowerField

/-!
# Lemma VII.7.3: prime-power local blocks

This file instantiates the full cyclotomic local-degree calculation in the
cyclic fixed fields constructed for odd and two-primary exponents.
-/

namespace Submission.CField.CBrauer

open AbsoluteValue IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.ICohomo

noncomputable section

universe u

/-- Choose one odd-primary conductor exponent which works at every prime in
the finite set and is at least the requested global-degree exponent. -/
theorem odd_uniform_conductor
    (S : Finset (finitePrime ℚ))
    (ell a : ℕ) (hell : ell.Prime) (hell2 : ell ≠ 2) :
    ∃ R : ℕ, a ≤ R ∧ ∀ P : S,
      Rat.HeightOneSpectrum.natGenerator P.1 ≠ ell →
        ell ^ a ∣ orderOf
          (Rat.HeightOneSpectrum.natGenerator P.1 : ZMod (ell ^ (R + 1))) := by
  let property : S → ℕ → Prop := fun P R ↦
    a ≤ R ∧ (Rat.HeightOneSpectrum.natGenerator P.1 ≠ ell →
      ell ^ a ∣ orderOf
        (Rat.HeightOneSpectrum.natGenerator P.1 : ZMod (ell ^ (R + 1))))
  have hmono : ∀ P r s, r ≤ s → property P r → property P s := by
    intro P r s hrs hr
    refine ⟨hr.1.trans hrs, ?_⟩
    intro hpell
    exact hr.2 hpell |>.trans
      (order_cast_dvd
        (Rat.HeightOneSpectrum.natGenerator P.1) ell (r + 1) (s + 1)
        (Nat.add_le_add_right hrs 1))
  have hexists : ∀ P, ∃ R, property P R := by
    intro P
    by_cases hpell : Rat.HeightOneSpectrum.natGenerator P.1 = ell
    · exact ⟨a, le_rfl, fun h ↦ (h hpell).elim⟩
    · have hp : (Rat.HeightOneSpectrum.natGenerator P.1).Prime :=
        Rat.HeightOneSpectrum.prime_natGenerator P.1
      obtain ⟨r, hr⟩ := odd_dvd_order
        (Rat.HeightOneSpectrum.natGenerator P.1) ell a hp hell hell2 hpell
      refine ⟨a + r, Nat.le_add_right a r, fun _ ↦ ?_⟩
      exact hr.trans (order_cast_dvd
        (Rat.HeightOneSpectrum.natGenerator P.1) ell r (a + r + 1)
        (by omega))
  obtain ⟨R, hR⟩ := exists_uniform_exponent property hmono hexists
  refine ⟨R + a, Nat.le_add_left a R, ?_⟩
  intro P
  exact (hmono P R (R + a) (Nat.le_add_right R a) (hR P)).2

set_option synthInstance.maxHeartbeats 1000000 in
-- The proof installs three compatible completion algebras for every prime.
set_option maxHeartbeats 5000000 in
/-- The odd-primary local-growth core of Lemma VII.7.3. -/
theorem oddGrowthCore :
    OddGrowthCore := by
  intro S ell a _hS _ha hell hell2
  obtain ⟨R, haR, horders⟩ :=
    odd_uniform_conductor S ell a hell hell2
  rcases odd_overfield_witness ell R hell hell2 with
    ⟨C, fieldC, numberFieldC, cyclotomicC, E, numberFieldE,
      galoisE, cyclicE, galoisEC, hEdegree, hrelative⟩
  letI : Field C := fieldC
  letI : NumberField C := numberFieldC
  letI : IsCyclotomicExtension {ell ^ (R + 1)} ℚ C := cyclotomicC
  letI : IsGalois ℚ C := cyclotomic_isGalois (n := ell ^ (R + 1))
  letI : NumberField E := numberFieldE
  letI : IsGalois ℚ E := galoisE
  letI : IsCyclic Gal(E/ℚ) := cyclicE
  letI : IsGalois E C := galoisEC
  let data : FEData ℚ :=
    { L := E
      fieldL := inferInstance
      numberFieldL := inferInstance
      algebraKL := E.algebra'
      finiteDimensionalKL := inferInstance
      isGaloisKL := galoisE }
  refine ⟨{
    extension := data
    isCyclicCyclotomic := ?_
    hasLocalDegrees := ?_
    degree_prime_power := ⟨R, hEdegree⟩ }⟩
  · change IsCyclic Gal(E/ℚ) ∧ _
    refine ⟨inferInstance, ell ^ (R + 1), C, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, trivial⟩
  · let fullPlace : ∀ P : S,
        CompletionPlacesAbove (L := C) (FinitePlace.mk P.1).val :=
      fun P ↦ by
        let v := (FinitePlace.mk P.1).val
        letI : Fact v.IsNontrivial :=
          ⟨absolute_value_nontrivial P.1⟩
        letI : IsUltrametricDist v.Completion :=
          placeUltrametricDist P.1
        exact Classical.choice
          (absolute_value_extension (K := ℚ) (L := C) v)
    choose u huv hwu htower using fun P : S ↦ by
      let v := (FinitePlace.mk P.1).val
      letI : Fact v.IsNontrivial :=
        ⟨absolute_value_nontrivial P.1⟩
      letI : IsUltrametricDist v.Completion :=
        placeUltrametricDist P.1
      exact finrank_tower
        (K := ℚ) (L := C) E v (fullPlace P)
    let chosen : ∀ P : S,
        CompletionPlacesAbove (L := E) (FinitePlace.mk P.1).val :=
      fun P ↦ ⟨u P, huv P⟩
    refine ⟨chosen, ?_⟩
    intro P
    let v := (FinitePlace.mk P.1).val
    let w := fullPlace P
    let uP := u P
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P.1⟩
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist P.1
    have huNontrivial : uP.IsNontrivial :=
      absolute_extension_nontrivial v (chosen P)
    have huNA : IsNonarchimedean uP :=
      absolute_extension_nonarchimedean v (chosen P)
    letI : Fact uP.IsNontrivial := ⟨huNontrivial⟩
    letI : IsUltrametricDist uP.Completion :=
      absoluteUltrametricDist uP huNA
    letI : Algebra v.Completion uP.Completion :=
      (completionLies v uP (huv P)).toAlgebra
    letI : Algebra uP.Completion w.1.Completion :=
      (completionLies uP w.1 (hwu P)).toAlgebra
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    have hfullIdeal :
        ell ^ a ∣
          P.1.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers C) *
            P.1.asIdeal.inertiaDegIn (NumberField.RingOfIntegers C) := by
      rw [ramification_idx_span P.1 C,
        rational_deg_span P.1 C]
      exact dvd_ramification_inertia
        P.1 ell R a hell haR C (horders P)
    have hfull : ell ^ a ∣
        Module.finrank v.Completion w.1.Completion := by
      rw [ramification_idx_deg
        P.1 w]
      exact hfullIdeal
    let wAboveU : CompletionPlacesAbove (K := E) (L := C) uP :=
      ⟨w.1, hwu P⟩
    have hrel : Module.finrank uP.Completion w.1.Completion ∣ ell - 1 := by
      have h := finrank_dvd_global uP huNA wAboveU
      rwa [hrelative] at h
    exact odd_dvd_degree ell a
      (Module.finrank v.Completion w.1.Completion)
      (Module.finrank uP.Completion w.1.Completion)
      (Module.finrank v.Completion uP.Completion)
      hell (htower P) hrel hfull

/-- Choose one two-primary conductor exponent which works at every selected
prime and is at least the requested fixed-field degree exponent. -/
theorem two_uniform_conductor
    (S : Finset (finitePrime ℚ)) (a : ℕ) :
    ∃ R : ℕ, a ≤ R ∧ ∀ P : S,
      Rat.HeightOneSpectrum.natGenerator P.1 ≠ 2 →
        2 ^ (a + 1) ∣ orderOf
          (Rat.HeightOneSpectrum.natGenerator P.1 : ZMod (2 ^ (R + 2))) := by
  let property : S → ℕ → Prop := fun P R ↦
    a ≤ R ∧ (Rat.HeightOneSpectrum.natGenerator P.1 ≠ 2 →
      2 ^ (a + 1) ∣ orderOf
        (Rat.HeightOneSpectrum.natGenerator P.1 : ZMod (2 ^ (R + 2))))
  have hmono : ∀ P r s, r ≤ s → property P r → property P s := by
    intro P r s hrs hr
    refine ⟨hr.1.trans hrs, ?_⟩
    intro hp2
    exact hr.2 hp2 |>.trans
      (order_cast_dvd
        (Rat.HeightOneSpectrum.natGenerator P.1) 2 (r + 2) (s + 2)
        (Nat.add_le_add_right hrs 2))
  have hexists : ∀ P, ∃ R, property P R := by
    intro P
    by_cases hp2 : Rat.HeightOneSpectrum.natGenerator P.1 = 2
    · exact ⟨a, le_rfl, fun h ↦ (h hp2).elim⟩
    · have hp : (Rat.HeightOneSpectrum.natGenerator P.1).Prime :=
        Rat.HeightOneSpectrum.prime_natGenerator P.1
      obtain ⟨r, hr⟩ := two_dvd_order
        (Rat.HeightOneSpectrum.natGenerator P.1) (a + 1) hp hp2
      refine ⟨a + r, Nat.le_add_right a r, fun _ ↦ ?_⟩
      exact hr.trans (order_cast_dvd
        (Rat.HeightOneSpectrum.natGenerator P.1) 2 r (a + r + 2)
        (by omega))
  obtain ⟨R, hR⟩ := exists_uniform_exponent property hmono hexists
  refine ⟨R + a, Nat.le_add_left a R, ?_⟩
  intro P
  exact (hmono P R (R + a) (Nat.le_add_right R a) (hR P)).2

set_option synthInstance.maxHeartbeats 1000000 in
-- The proof installs three compatible completion algebras for every prime.
set_option maxHeartbeats 5000000 in
/-- The exceptional two-primary local-growth core, using the diagonal
order-two subgroup and retaining total complexity of the resulting block. -/
theorem complexGrowthCore :
    ComplexGrowthCore := by
  intro S a _hS ha
  obtain ⟨R, haR, horders⟩ :=
    two_uniform_conductor S a
  rcases complex_overfield_witness R
      (ha.trans_le haR) with
    ⟨C, fieldC, numberFieldC, cyclotomicC, E, numberFieldE,
      galoisE, cyclicE, galoisEC, totallyComplexE,
      hEdegree, hrelative⟩
  letI : Field C := fieldC
  letI : NumberField C := numberFieldC
  letI : IsCyclotomicExtension {2 ^ (R + 2)} ℚ C := cyclotomicC
  letI : IsGalois ℚ C := cyclotomic_isGalois (n := 2 ^ (R + 2))
  letI : NumberField E := numberFieldE
  letI : IsGalois ℚ E := galoisE
  letI : IsCyclic Gal(E/ℚ) := cyclicE
  letI : IsGalois E C := galoisEC
  letI : NumberField.IsTotallyComplex E := totallyComplexE
  let data : FEData ℚ :=
    { L := E
      fieldL := inferInstance
      numberFieldL := inferInstance
      algebraKL := E.algebra'
      finiteDimensionalKL := inferInstance
      isGaloisKL := galoisE }
  refine ⟨⟨{
    extension := data
    isCyclicCyclotomic := ?_
    hasLocalDegrees := ?_
    degree_prime_power := ⟨R, hEdegree⟩ }, ?_⟩⟩
  · change IsCyclic Gal(E/ℚ) ∧ _
    refine ⟨inferInstance, 2 ^ (R + 2), C, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, trivial⟩
  · let fullPlace : ∀ P : S,
        CompletionPlacesAbove (L := C) (FinitePlace.mk P.1).val :=
      fun P ↦ by
        let v := (FinitePlace.mk P.1).val
        letI : Fact v.IsNontrivial :=
          ⟨absolute_value_nontrivial P.1⟩
        letI : IsUltrametricDist v.Completion :=
          placeUltrametricDist P.1
        exact Classical.choice
          (absolute_value_extension (K := ℚ) (L := C) v)
    choose u huv hwu htower using fun P : S ↦ by
      let v := (FinitePlace.mk P.1).val
      letI : Fact v.IsNontrivial :=
        ⟨absolute_value_nontrivial P.1⟩
      letI : IsUltrametricDist v.Completion :=
        placeUltrametricDist P.1
      exact finrank_tower
        (K := ℚ) (L := C) E v (fullPlace P)
    let chosen : ∀ P : S,
        CompletionPlacesAbove (L := E) (FinitePlace.mk P.1).val :=
      fun P ↦ ⟨u P, huv P⟩
    refine ⟨chosen, ?_⟩
    intro P
    let v := (FinitePlace.mk P.1).val
    let w := fullPlace P
    let uP := u P
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P.1⟩
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist P.1
    have huNontrivial : uP.IsNontrivial :=
      absolute_extension_nontrivial v (chosen P)
    have huNA : IsNonarchimedean uP :=
      absolute_extension_nonarchimedean v (chosen P)
    letI : Fact uP.IsNontrivial := ⟨huNontrivial⟩
    letI : IsUltrametricDist uP.Completion :=
      absoluteUltrametricDist uP huNA
    letI : Algebra v.Completion uP.Completion :=
      (completionLies v uP (huv P)).toAlgebra
    letI : Algebra uP.Completion w.1.Completion :=
      (completionLies uP w.1 (hwu P)).toAlgebra
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    have hfullIdeal :
        2 ^ (a + 1) ∣
          P.1.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers C) *
            P.1.asIdeal.inertiaDegIn (NumberField.RingOfIntegers C) := by
      rw [ramification_idx_span P.1 C,
        rational_deg_span P.1 C]
      apply dvd_ramification_inertia
        P.1 2 (R + 1) (a + 1) Nat.prime_two
        (Nat.add_le_add_right haR 1) C
      simpa only [Nat.add_assoc] using horders P
    have hfull : 2 ^ (a + 1) ∣
        Module.finrank v.Completion w.1.Completion := by
      rw [ramification_idx_deg
        P.1 w]
      exact hfullIdeal
    let wAboveU : CompletionPlacesAbove (K := E) (L := C) uP :=
      ⟨w.1, hwu P⟩
    have hrel : Module.finrank uP.Completion w.1.Completion ∣ 2 := by
      have h := finrank_dvd_global uP huNA wAboveU
      rwa [hrelative] at h
    exact dvd_fixed_degree a
      (Module.finrank v.Completion w.1.Completion)
      (Module.finrank uP.Completion w.1.Completion)
      (Module.finrank v.Completion uP.Completion)
      (htower P) hrel hfull
  · exact totallyComplexE

/-- Forgetting total complexity gives the original two-primary growth
bridge. -/
theorem twoGrowthCore :
    TwoGrowthCore := by
  intro S a hS ha
  obtain ⟨block, _hcomplex⟩ :=
    complexGrowthCore S a hS ha
  exact ⟨block⟩

/-- A totally complex two-primary block is always available.  Its exponent
is `max 1 a`: for positive `a` this supplies the requested two-primary
factor, while for `a = 0` it is the auxiliary quadratic complex factor
needed to make an odd-degree requested compositum totally complex. -/
theorem complex_two_block
    (S : Finset (finitePrime ℚ)) (a : ℕ) :
    Nonempty {block : RationalPrimeBlock S 2 (max 1 a) //
      block.extension.IsTotallyComplex} := by
  have hpositive : 0 < max 1 a := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 a)
  by_cases hS : S.Nonempty
  · exact complexGrowthCore
      S (max 1 a) hS hpositive
  · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    rcases complex_extension_data
        (max 1 a) hpositive with
      ⟨data, hcyclic, hcomplex, hdegree⟩
    let block : RationalPrimeBlock ∅ 2 (max 1 a) :=
      { extension := data
        isCyclicCyclotomic := hcyclic
        hasLocalDegrees := by
          dsimp only [FEData.LocalDegreesDvd]
          refine ⟨fun P ↦ ?_, ?_⟩
          · exact nomatch P.property
          · intro P
            exact nomatch P.property
        degree_prime_power := ⟨max 1 a, hdegree⟩ }
    exact ⟨⟨block, hcomplex⟩⟩

/-- The complete positive-exponent, nonempty-set prime-power growth core is
unconditional. -/
theorem growthCoreBridge :
    GrowthCoreBridge :=
  growth_core_odd
    oddGrowthCore
    twoGrowthCore

/-- Including the trivial zero-exponent and empty-set cases, rational
prime-power blocks now exist unconditionally. -/
theorem rationalGrowthBridge :
    RationalGrowthBridge :=
  growth_bridge_core
    growthCoreBridge

/-- With prime-power growth discharged, Lemma VII.7.3 now depends only on
the coprime cyclic-compositum construction and rational base change. -/
theorem blocks_compositum_change
    (hcompositum : RationalCompositumBridge)
    (hbaseChange : ChangeRationalsBridge.{u}) :
    (∀ (K : Type u) [Field K] [NumberField K]
          (S : Finset (finitePrime K)) (m : ℕ),
          0 < m →
            ∃ data : FEData K,
              data.IsCyclicCyclotomic ∧
                data.IsTotallyComplex ∧
                data.LocalDegreesDvd S m) :=
  below_arithmetic_bridges
    rationalGrowthBridge hcompositum hbaseChange

/-- The exact remaining two-bridge boundary consumed by Proposition VII.7.2. -/
theorem primePowerBlocks
    (hcompositum : RationalCompositumBridge)
    (hbaseChange : ChangeRationalsBridge.{u}) :
    FinitePrime.{u} :=
  prime_rational_bridges
    rationalGrowthBridge hcompositum hbaseChange

end

end Submission.CField.CBrauer
