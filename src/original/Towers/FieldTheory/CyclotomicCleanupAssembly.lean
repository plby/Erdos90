import Towers.FieldTheory.RationalCyclotomicCleanup
import Mathlib.RingTheory.Ideal.GoingUp

open scoped Pointwise Topology

noncomputable section

namespace Towers
namespace TBluepr

universe u v

local instance cleanupAssemblyFiniteDimensional
    (D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    FiniteDimensional ℚ D :=
  D.finiteDimensional

local instance cleanupAssemblyIsGalois
    (D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    IsGalois ℚ D :=
  D.isGalois

/-- The finite set of ramified rational prime ideals of `D` whose rational
prime is outside `S` and distinct from `3`. -/
noncomputable def ramifiedIdealsFinset
    (D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (S : Finset ℕ) :
    Finset (Ideal (NumberField.RingOfIntegers ℚ)) :=
  (ramifiedBaseFinset ℚ D).filter fun p =>
    Ideal.absNorm (p.map Rat.ringOfIntegersEquiv) ∉ S ∧
      Ideal.absNorm (p.map Rat.ringOfIntegersEquiv) ≠ 3

/-- An index for each rational prime that is ramified in `D`, outside `S`,
and distinct from `3`. -/
abbrev TRIndex
    (D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (S : Finset ℕ) :=
  {p // p ∈ ramifiedIdealsFinset D S}

/-- The rational prime associated with a tame ramified-prime index. -/
def TRIndex.prime
    {D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)}
    {S : Finset ℕ} (i : TRIndex D S) : ℕ :=
  Ideal.absNorm (i.1.map Rat.ringOfIntegersEquiv)

private theorem tame_ramified_above
    {D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)}
    {S : Finset ℕ} (i : TRIndex D S) :
    ∃ P : Ideal (NumberField.RingOfIntegers D),
      P.IsPrime ∧ P ≠ ⊥ ∧
        P.under (NumberField.RingOfIntegers ℚ) = i.1 ∧
        Ideal.ramificationIdx i.1 P ≠ 1 := by
  have hi : i.1 ∈ ramifiedBaseFinset ℚ D :=
    (Finset.mem_filter.mp i.2).1
  exact (ramified_ideals_finset ℚ D i.1).mp hi

/-- A chosen ramified prime of `D` over a tame ramified-prime index. -/
noncomputable def TRIndex.primeAbove
    {D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)}
    {S : Finset ℕ} (i : TRIndex D S) :
    Ideal (NumberField.RingOfIntegers D) :=
  Classical.choose (tame_ramified_above i)

theorem TRIndex.prime_above
    {D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)}
    {S : Finset ℕ} (i : TRIndex D S) :
    i.primeAbove.IsPrime :=
  (Classical.choose_spec (tame_ramified_above i)).1

theorem TRIndex.prime_above_nebot
    {D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)}
    {S : Finset ℕ} (i : TRIndex D S) :
    i.primeAbove ≠ ⊥ :=
  (Classical.choose_spec (tame_ramified_above i)).2.1

theorem TRIndex.primeAbove_under
    {D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)}
    {S : Finset ℕ} (i : TRIndex D S) :
    i.primeAbove.under (NumberField.RingOfIntegers ℚ) = i.1 :=
  (Classical.choose_spec
    (tame_ramified_above i)).2.2.1

theorem TRIndex.ramif_idx_neone
    {D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)}
    {S : Finset ℕ} (i : TRIndex D S) :
    Ideal.ramificationIdx i.1 i.primeAbove ≠ 1 :=
  (Classical.choose_spec
    (tame_ramified_above i)).2.2.2

theorem TRIndex.prime_isPrime
    {D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)}
    {S : Finset ℕ} (i : TRIndex D S) :
    Nat.Prime i.prime := by
  let J : Ideal ℤ := i.1.map Rat.ringOfIntegersEquiv
  letI : i.primeAbove.IsPrime := i.prime_above
  have hiprime : i.1.IsPrime := by
    rw [← i.primeAbove_under]
    infer_instance
  letI : i.1.IsPrime := hiprime
  have hJprime : J.IsPrime :=
    Ideal.map_isPrime_of_equiv Rat.ringOfIntegersEquiv
  letI : J.IsPrime := hJprime
  have hJne : J ≠ ⊥ := by
    intro hbot
    have hiBot : i.1 = ⊥ :=
      (Ideal.map_eq_bot_iff_of_injective
        Rat.ringOfIntegersEquiv.injective).mp hbot
    have hiNe : i.1 ≠ ⊥ := by
      rw [← i.primeAbove_under]
      exact Ideal.under_ne_bot
        (NumberField.RingOfIntegers ℚ) i.prime_above_nebot
    exact hiNe hiBot
  letI : NeZero J := ⟨hJne⟩
  have h := Nat.absNorm_under_prime J
  simpa [TRIndex.prime, J] using h

theorem TRIndex.prime_ne_three
    {D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)}
    {S : Finset ℕ} (i : TRIndex D S) :
    i.prime ≠ 3 :=
  (Finset.mem_filter.mp i.2).2.2

theorem TRIndex.prime_not_mem
    {D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)}
    {S : Finset ℕ} (i : TRIndex D S) :
    i.prime ∉ S :=
  (Finset.mem_filter.mp i.2).2.1

theorem TRIndex.rational_prime_idealeq
    {D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)}
    {S : Finset ℕ} (i : TRIndex D S) :
    Ideal.rationalPrimeIdeal i.prime =
      i.1.map Rat.ringOfIntegersEquiv := by
  simp [TRIndex.prime, Ideal.rationalPrimeIdeal]

theorem TRIndex.prime_above_lies
    {D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)}
    {S : Finset ℕ} (i : TRIndex D S) :
    i.primeAbove.LiesOver (Ideal.rationalPrimeIdeal i.prime) := by
  constructor
  rw [i.rational_prime_idealeq]
  calc
    i.1.map Rat.ringOfIntegersEquiv =
        (i.primeAbove.under (NumberField.RingOfIntegers ℚ)).map
          Rat.ringOfIntegersEquiv := by rw [i.primeAbove_under]
    _ = i.primeAbove.under ℤ := by
      let e0 := Rat.ringOfIntegersEquiv
      have halg : (algebraMap ℤ (NumberField.RingOfIntegers ℚ)) =
          e0.symm.toRingHom :=
        Subsingleton.elim _ _
      rw [← Ideal.under_under
        (A := ℤ) (B := NumberField.RingOfIntegers ℚ)
          (C := NumberField.RingOfIntegers D)]
      change _ = (i.primeAbove.under
        (NumberField.RingOfIntegers ℚ)).comap
          (algebraMap ℤ (NumberField.RingOfIntegers ℚ))
      rw [halg]
      exact Ideal.map_comap_of_equiv
        (I := i.primeAbove.under (NumberField.RingOfIntegers ℚ)) e0

theorem TRIndex.prime_injective
    {D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)}
    {S : Finset ℕ} :
    Function.Injective
      (fun i : TRIndex D S => i.prime) := by
  intro i j hij
  change i.prime = j.prime at hij
  apply Subtype.ext
  have hmap : i.1.map Rat.ringOfIntegersEquiv =
      j.1.map Rat.ringOfIntegersEquiv := by
    calc
      _ = Ideal.rationalPrimeIdeal i.prime := i.rational_prime_idealeq.symm
      _ = Ideal.rationalPrimeIdeal j.prime :=
        congrArg Ideal.rationalPrimeIdeal hij
      _ = _ := j.rational_prime_idealeq
  calc
    i.1 = (i.1.map Rat.ringOfIntegersEquiv).comap
        Rat.ringOfIntegersEquiv :=
      (Ideal.comap_map_of_bijective _
        Rat.ringOfIntegersEquiv.bijective).symm
    _ = (j.1.map Rat.ringOfIntegersEquiv).comap
        Rat.ringOfIntegersEquiv := congrArg _ hmap
    _ = j.1 := Ideal.comap_map_of_bijective _
      Rat.ringOfIntegersEquiv.bijective

theorem TRIndex.prime_mod_eqone
    {D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)}
    {S : Finset ℕ}
    (hDthree : IsPGroup 3 Gal(D/ℚ))
    (i : TRIndex D S) :
    i.prime ≡ 1 [MOD 3] := by
  let P := i.primeAbove
  letI : P.IsPrime := i.prime_above
  letI : P.IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance i.prime_above_nebot
  letI : P.LiesOver (Ideal.rationalPrimeIdeal i.prime) :=
    i.prime_above_lies
  letI : P.LiesOver i.1 := ⟨i.primeAbove_under.symm⟩
  letI : i.1.IsPrime := by
    rw [← i.primeAbove_under]
    infer_instance
  have hi0 : i.1 ≠ ⊥ := by
    rw [← i.primeAbove_under]
    exact Ideal.under_ne_bot
      (NumberField.RingOfIntegers ℚ) i.prime_above_nebot
  letI : i.1.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hi0
  letI : Field (NumberField.RingOfIntegers ℚ ⧸ i.1) :=
    Ideal.Quotient.field i.1
  letI : Field (NumberField.RingOfIntegers D ⧸ P) :=
    Ideal.Quotient.field P
  letI : Finite (NumberField.RingOfIntegers ℚ ⧸ i.1) := inferInstance
  letI : PerfectField (NumberField.RingOfIntegers ℚ ⧸ i.1) :=
    PerfectField.ofFinite
  letI : Finite (NumberField.RingOfIntegers D ⧸ P) := inferInstance
  letI : Module.Finite (NumberField.RingOfIntegers ℚ ⧸ i.1)
      (NumberField.RingOfIntegers D ⧸ P) := Module.Finite.of_finite
  letI : Algebra.IsSeparable (NumberField.RingOfIntegers ℚ ⧸ i.1)
      (NumberField.RingOfIntegers D ⧸ P) := inferInstance
  letI : IsGaloisGroup Gal(D/ℚ) (NumberField.RingOfIntegers ℚ)
      (NumberField.RingOfIntegers D) :=
    IsGaloisGroup.of_isFractionRing Gal(D/ℚ)
      (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers D) ℚ D
  have hIne : P.inertia Gal(D/ℚ) ≠ ⊥ := by
    intro hbot
    have hp0 : i.1 ≠ ⊥ := by
      exact hi0
    have hcard : Nat.card (P.inertia Gal(D/ℚ)) =
        Ideal.ramificationIdx i.1 P := by
      calc
        _ = Ideal.ramificationIdxIn i.1
            (NumberField.RingOfIntegers D) :=
          Ideal.card_inertia_eq_ramificationIdxIn
            (G := Gal(D/ℚ)) i.1 hp0 P
        _ = _ := Ideal.ramificationIdxIn_eq_ramificationIdx
          (G := Gal(D/ℚ)) (p := i.1) (P := P)
    have hcardOne : Nat.card (P.inertia Gal(D/ℚ)) = 1 := by
      rw [hbot]
      simp
    apply i.ramif_idx_neone
    rw [← hcard, hcardOne]
  exact rational_inertia_bot
    D hDthree i.prime_isPrime i.prime_ne_three P hIne

/-!
## The canonical common ambient compositum

The point of the following definitions is to remove the artificial ambient
field parameter from the finite-family cleanup theorem.  We take the
compositum of the original finite three-extension and every cubic
cyclotomic correction field indexed by its tame ramified primes.
-/

/-- The finite family consisting of the original lift field (`none`) and
the cubic cyclotomic correction field at each tame ramified prime (`some i`). -/
noncomputable def tameCyclotomicFamily
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ) :
    Option (TRIndex D0 S) →
      IntermediateField ℚ (AlgebraicClosure ℚ)
  | none => D0.toIntermediateField
  | some i =>
      rationalCyclotomicCubic i.prime i.prime_isPrime
        (i.prime_mod_eqone hD0three)

/-- The common finite Galois field containing the lift field and all tame
cyclotomic correction fields. -/
noncomputable def tameCorrectionCompositum
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ) :
    FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) := by
  let family := tameCyclotomicFamily D0 hD0three S
  let U : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    Finset.univ.sup family
  letI : Algebra ℚ U := U.algebra'
  letI : FiniteDimensional ℚ U :=
    finset_sup_dimensional family Finset.univ (fun o => by
      cases o with
      | none => exact D0.finiteDimensional
      | some i =>
          change FiniteDimensional ℚ
            (rationalCyclotomicCubic i.prime i.prime_isPrime
              (i.prime_mod_eqone hD0three))
          infer_instance)
  letI : IsGalois ℚ U :=
    finset_sup_galois family Finset.univ (fun o => by
      cases o with
      | none => exact D0.isGalois
      | some i =>
          exact (rational_cubic_galois
            i.prime i.prime_isPrime
              (i.prime_mod_eqone hD0three)).2.1)
  exact
    { toIntermediateField := U
      finiteDimensional := inferInstance
      isGalois := inferInstance }

theorem tame_cyclotomic_compositum
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ)
    (o : Option (TRIndex D0 S)) :
    tameCyclotomicFamily D0 hD0three S o ≤
      (tameCorrectionCompositum D0 hD0three S).toIntermediateField := by
  exact Finset.le_sup (f := tameCyclotomicFamily D0 hD0three S)
    (Finset.mem_univ o)

/-- The original lift field, as an intermediate field of the common
correction compositum. -/
noncomputable def tameLiftCompositum
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ) :
    IntermediateField ℚ (tameCorrectionCompositum D0 hD0three S) :=
  D0.toIntermediateField.restrict
    (tame_cyclotomic_compositum
      D0 hD0three S none)

/-- The canonical equivalence from the original lift field to its copy in
the common correction compositum. -/
noncomputable def tameCyclotomicCompositum
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ) :
    D0 ≃ₐ[ℚ] tameLiftCompositum D0 hD0three S :=
  IntermediateField.restrict_algEquiv
    (tame_cyclotomic_compositum
      D0 hD0three S none)

/-- Every member of the defining family, viewed inside the common
compositum. -/
noncomputable def tameFamilyCompositum
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ)
    (o : Option (TRIndex D0 S)) :
    IntermediateField ℚ (tameCorrectionCompositum D0 hD0three S) :=
  (tameCyclotomicFamily D0 hD0three S o).restrict
    (tame_cyclotomic_compositum D0 hD0three S o)

set_option maxHeartbeats 2000000 in
-- The finite supremum proof unfolds the correction-family compositum.
theorem compositum_sup_top
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ) :
    Finset.univ.sup
      (tameFamilyCompositum D0 hD0three S) = ⊤ := by
  let D := tameCorrectionCompositum D0 hD0three S
  let family := tameCyclotomicFamily D0 hD0three S
  let familyD := tameFamilyCompositum
    D0 hD0three S
  let A : IntermediateField ℚ D := Finset.univ.sup familyD
  change A = ⊤
  apply IntermediateField.lift_injective D.toIntermediateField
  change IntermediateField.lift A =
    IntermediateField.lift (⊤ : IntermediateField ℚ D)
  rw [show IntermediateField.lift
      (⊤ : IntermediateField ℚ D) = D.toIntermediateField by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, by simp, rfl⟩]
  apply le_antisymm
  · exact IntermediateField.lift_le A
  · change Finset.univ.sup family ≤ IntermediateField.lift A
    apply Finset.sup_le
    intro o ho
    have hcomponent : familyD o ≤ A :=
      Finset.le_sup (f := familyD) (Finset.mem_univ o)
    have hlift : IntermediateField.lift (familyD o) ≤
        IntermediateField.lift A :=
      IntermediateField.map_mono D.toIntermediateField.val hcomponent
    simpa [familyD,
      tameFamilyCompositum,
      IntermediateField.lift_restrict] using hlift

/-- The correction cubic field at `i`, as an intermediate field of the
common correction compositum. -/
noncomputable def cyclotomicCubicCompositum
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ)
    (i : TRIndex D0 S) :
    IntermediateField ℚ (tameCorrectionCompositum D0 hD0three S) :=
  (rationalCyclotomicCubic i.prime i.prime_isPrime
      (i.prime_mod_eqone hD0three)).restrict
    (tame_cyclotomic_compositum
      D0 hD0three S (some i))

/-- The canonical equivalence from the abstract cubic cyclotomic field to
its copy inside the common correction compositum. -/
noncomputable def tameCubicCompositum
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ)
    (i : TRIndex D0 S) :
    rationalCyclotomicCubic i.prime i.prime_isPrime
        (i.prime_mod_eqone hD0three) ≃ₐ[ℚ]
      cyclotomicCubicCompositum D0 hD0three S i :=
  IntermediateField.restrict_algEquiv
    (tame_cyclotomic_compositum
      D0 hD0three S (some i))

theorem tame_compositum_dimensional
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ)
    (i : TRIndex D0 S) :
    let C := cyclotomicCubicCompositum D0 hD0three S i
    letI : Algebra ℚ C := C.algebra'
    FiniteDimensional ℚ C := by
  dsimp only
  exact Module.Finite.equiv
    (tameCubicCompositum
      D0 hD0three S i).toLinearEquiv

theorem tame_compositum_galois
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ)
    (i : TRIndex D0 S) :
    let C := cyclotomicCubicCompositum D0 hD0three S i
    letI : Algebra ℚ C := C.algebra'
    IsGalois ℚ C := by
  dsimp only
  let C0 := rationalCyclotomicCubic i.prime i.prime_isPrime
    (i.prime_mod_eqone hD0three)
  letI : IsGalois ℚ C0 :=
    (rational_cubic_galois
      i.prime i.prime_isPrime (i.prime_mod_eqone hD0three)).2.1
  exact IsGalois.of_algEquiv
    (tameCubicCompositum
      D0 hD0three S i)

private theorem tame_compositum_above
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ)
    (i : TRIndex D0 S) :
    ∃ P : Ideal (NumberField.RingOfIntegers
        (tameCorrectionCompositum D0 hD0three S)),
      P.IsMaximal ∧
        P.LiesOver (Ideal.rationalPrimeIdeal i.prime) := by
  let D := tameCorrectionCompositum D0 hD0three S
  let p : Ideal ℤ := Ideal.rationalPrimeIdeal i.prime
  letI : p.IsMaximal := rational_ideal_maximal i.prime_isPrime
  obtain ⟨P, hPmax, hPover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral p
      (S := NumberField.RingOfIntegers D)
  exact ⟨P, hPmax, hPover⟩

/-- A chosen prime of the common correction compositum over the indexed
rational prime. -/
noncomputable def tameCyclotomicAbove
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ)
    (i : TRIndex D0 S) :
    Ideal (NumberField.RingOfIntegers
      (tameCorrectionCompositum D0 hD0three S)) :=
  Classical.choose
    (tame_compositum_above
      D0 hD0three S i)

theorem tame_cyclotomic_above
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ)
    (i : TRIndex D0 S) :
    (tameCyclotomicAbove D0 hD0three S i).IsPrime :=
  (Classical.choose_spec
    (tame_compositum_above
      D0 hD0three S i)).1.isPrime

theorem tame_above_lies
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ)
    (i : TRIndex D0 S) :
    (tameCyclotomicAbove D0 hD0three S i).LiesOver
      (Ideal.rationalPrimeIdeal i.prime) :=
  (Classical.choose_spec
    (tame_compositum_above
      D0 hD0three S i)).2

theorem tame_compositum_idx
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ)
    (i : TRIndex D0 S) :
    let C := cyclotomicCubicCompositum D0 hD0three S i
    let P := tameCyclotomicAbove D0 hD0three S i
    letI : Algebra ℚ C := C.algebra'
    letI : FiniteDimensional ℚ C := inferInstance
    letI : NumberField C := NumberField.of_module_finite ℚ C
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal i.prime)
      (P.under (NumberField.RingOfIntegers C)) = 3 := by
  dsimp only
  let D := tameCorrectionCompositum D0 hD0three S
  let C := cyclotomicCubicCompositum D0 hD0three S i
  let C0 := rationalCyclotomicCubic i.prime i.prime_isPrime
    (i.prime_mod_eqone hD0three)
  let P := tameCyclotomicAbove D0 hD0three S i
  let e : C0 ≃ₐ[ℚ] C :=
    tameCubicCompositum D0 hD0three S i
  let eO : NumberField.RingOfIntegers C0 ≃ₐ[ℤ]
      NumberField.RingOfIntegers C :=
    (e.restrictScalars ℤ).mapIntegralClosure
  let Qc : Ideal (NumberField.RingOfIntegers C) :=
    P.under (NumberField.RingOfIntegers C)
  let Q0 : Ideal (NumberField.RingOfIntegers C0) := Qc.comap eO
  letI : P.IsPrime :=
    tame_cyclotomic_above D0 hD0three S i
  letI : P.LiesOver (Ideal.rationalPrimeIdeal i.prime) :=
    tame_above_lies D0 hD0three S i
  have hQc : Qc ∈ (Ideal.rationalPrimeIdeal i.prime).primesOver
      (NumberField.RingOfIntegers C) := by
    exact ⟨inferInstance, inferInstance⟩
  letI : Qc.IsPrime := hQc.1
  letI : Qc.LiesOver (Ideal.rationalPrimeIdeal i.prime) := hQc.2
  have hQ0 : Q0 ∈ (Ideal.rationalPrimeIdeal i.prime).primesOver
      (NumberField.RingOfIntegers C0) := by
    exact ⟨inferInstance, inferInstance⟩
  calc
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal i.prime) Qc =
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal i.prime) Q0 := by
      symm
      exact (Ideal.rationalPrimeIdeal i.prime).ramificationIdx_comap_eq eO Qc
    _ = 3 :=
      cubic_ramification_idx
        i.prime i.prime_isPrime (i.prime_mod_eqone hD0three) Q0 hQ0

theorem tame_compositum_card
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ)
    (i : TRIndex D0 S) :
    let C := cyclotomicCubicCompositum D0 hD0three S i
    letI : Algebra ℚ C := C.algebra'
    letI : FiniteDimensional ℚ C := inferInstance
    Nat.card Gal(C/ℚ) = 3 := by
  dsimp only
  let C0 := rationalCyclotomicCubic i.prime i.prime_isPrime
    (i.prime_mod_eqone hD0three)
  let C := cyclotomicCubicCompositum D0 hD0three S i
  let e : C0 ≃ₐ[ℚ] C :=
    tameCubicCompositum D0 hD0three S i
  letI : IsGalois ℚ C0 :=
    (rational_cubic_galois
      i.prime i.prime_isPrime (i.prime_mod_eqone hD0three)).2.1
  calc
    Nat.card Gal(C/ℚ) = Nat.card Gal(C0/ℚ) :=
      Nat.card_congr (AlgEquiv.autCongr e).toEquiv.symm
    _ = Module.finrank ℚ C0 := IsGalois.card_aut_eq_finrank ℚ C0
    _ = 3 :=
      (rational_cubic_galois
        i.prime i.prime_isPrime (i.prime_mod_eqone hD0three)).1

/-- Restriction from the common correction compositum to the original lift
field. -/
noncomputable def tameCyclotomicRestriction
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ) :
    Gal(tameCorrectionCompositum D0 hD0three S/ℚ) →* Gal(D0/ℚ) := by
  let E := tameLiftCompositum D0 hD0three S
  let eE := tameCyclotomicCompositum D0 hD0three S
  letI : IsGalois ℚ D0 := D0.isGalois
  letI : IsGalois ℚ E := IsGalois.of_algEquiv eE
  exact (AlgEquiv.autCongr eE).symm.toMonoidHom.comp
    (finiteIntermediateRestriction
      (tameCorrectionCompositum D0 hD0three S)
      E (inferInstance : Normal ℚ E))

set_option maxHeartbeats 4000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- Restriction through the correction compositum has a large field tower.
/-- Restricting an absolute automorphism first to the correction compositum
and then to its copy of the lift field agrees with direct restriction to the
original lift field. -/
@[simp]
theorem tame_restriction_restrict
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ)
    (sigma : Gal(AlgebraicClosure ℚ/ℚ)) :
    tameCyclotomicRestriction D0 hD0three S
        (AlgEquiv.restrictNormalHom
          (tameCorrectionCompositum
            D0 hD0three S).toIntermediateField sigma) =
      AlgEquiv.restrictNormalHom D0.toIntermediateField sigma := by
  let D := tameCorrectionCompositum D0 hD0three S
  let E := tameLiftCompositum D0 hD0three S
  let eE := tameCyclotomicCompositum D0 hD0three S
  let hEgal : IsGalois ℚ E := by
    letI : IsGalois ℚ D0 := D0.isGalois
    exact IsGalois.of_algEquiv eE
  letI : Algebra ℚ E := E.algebra'
  letI : Algebra E D := E.toAlgebra
  letI : IsScalarTower ℚ E D := IsScalarTower.of_algebraMap_eq' rfl
  letI : Normal ℚ E := hEgal.to_normal
  change (AlgEquiv.autCongr eE).symm
      (AlgEquiv.restrictNormalHom E
        (AlgEquiv.restrictNormalHom D.toIntermediateField sigma)) =
    AlgEquiv.restrictNormalHom D0.toIntermediateField sigma
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  let rhoD := AlgEquiv.restrictNormalHom D.toIntermediateField sigma
  let rhoE := AlgEquiv.restrictNormalHom E rhoD
  have he (y : E) :
      ((eE.symm y : D0) : AlgebraicClosure ℚ) =
        (((y : E) : D) : AlgebraicClosure ℚ) := by
    have h := eE.apply_symm_apply y
    exact congrArg
      (fun z : E => (((z : E) : D) : AlgebraicClosure ℚ)) h
  calc
    (((AlgEquiv.autCongr eE).symm rhoE x : D0) : AlgebraicClosure ℚ) =
        ((eE.symm (rhoE (eE x)) : D0) : AlgebraicClosure ℚ) := rfl
    _ = (((rhoE (eE x) : E) : D) : AlgebraicClosure ℚ) :=
      he (rhoE (eE x))
    _ = ((rhoD ((eE x : E) : D) : D) : AlgebraicClosure ℚ) := by
      exact congrArg (fun z : D => (z : AlgebraicClosure ℚ))
        (@AlgEquiv.restrictNormalHom_apply ℚ inferInstance D
          inferInstance inferInstance E hEgal.to_normal rhoD (eE x))
    _ = sigma ((((eE x : E) : D) : AlgebraicClosure ℚ)) := by
      exact @AlgEquiv.restrictNormalHom_apply ℚ inferInstance
        (AlgebraicClosure ℚ) inferInstance inferInstance D
        D.isGalois.to_normal sigma ((eE x : E) : D)
    _ = sigma (x : AlgebraicClosure ℚ) := by rfl
    _ = ((AlgEquiv.restrictNormalHom D0.toIntermediateField sigma x : D0) :
          AlgebraicClosure ℚ) :=
      (@AlgEquiv.restrictNormalHom_apply ℚ inferInstance
        (AlgebraicClosure ℚ) inferInstance inferInstance D0
        D0.isGalois.to_normal sigma x).symm

set_option maxHeartbeats 4000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- Joint inertia detection synthesizes every field in the correction family.
/-- At the prime indexed by `i`, restriction to the original lift field and
to the `i`th cyclotomic cubic field jointly detects ambient inertia.  The
other correction fields are unramified there, so their restrictions vanish;
the defining family generates the whole common compositum. -/
theorem tame_restriction_injective
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ)
    (i : TRIndex D0 S) :
    let D := tameCorrectionCompositum D0 hD0three S
    let C := cyclotomicCubicCompositum D0 hD0three S i
    let P := tameCyclotomicAbove D0 hD0three S i
    letI : Algebra ℚ C := C.algebra'
    let hCgal : IsGalois ℚ C :=
      tame_compositum_galois D0 hD0three S i
    letI : P.IsPrime :=
      tame_cyclotomic_above D0 hD0three S i
    letI : P.LiesOver (Ideal.rationalPrimeIdeal i.prime) :=
      tame_above_lies D0 hD0three S i
    Function.Injective
      ((((tameCyclotomicRestriction D0 hD0three S).comp
          (P.inertia Gal(D/ℚ)).subtype).prod
        (numberInertiaRestriction C hCgal.to_normal i.prime P))) := by
  dsimp only
  let D := tameCorrectionCompositum D0 hD0three S
  let E := tameLiftCompositum D0 hD0three S
  let C := cyclotomicCubicCompositum D0 hD0three S i
  let P := tameCyclotomicAbove D0 hD0three S i
  let eE := tameCyclotomicCompositum D0 hD0three S
  let familyD := tameFamilyCompositum
    D0 hD0three S
  letI : P.IsPrime :=
    tame_cyclotomic_above D0 hD0three S i
  letI : P.LiesOver (Ideal.rationalPrimeIdeal i.prime) :=
    tame_above_lies D0 hD0three S i
  let hEgal : IsGalois ℚ E := by
    letI : IsGalois ℚ D0 := D0.isGalois
    exact IsGalois.of_algEquiv eE
  letI : IsGalois ℚ E := hEgal
  letI : Normal ℚ E := hEgal.to_normal
  let hCgal : IsGalois ℚ C :=
    tame_compositum_galois D0 hD0three S i
  letI : IsGalois ℚ C := hCgal
  letI : Normal ℚ C := hCgal.to_normal
  let first := (tameCyclotomicRestriction D0 hD0three S).comp
    (P.inertia Gal(D/ℚ)).subtype
  let second := numberInertiaRestriction C hCgal.to_normal i.prime P
  let pairHom := first.prod second
  change Function.Injective pairHom
  apply (injective_iff_map_eq_one pairHom).2
  intro sigma hsigma
  change (first sigma, second sigma) = (1, 1) at hsigma
  have hEone : AlgEquiv.restrictNormalHom E sigma.1 = 1 := by
    have hfirst : first sigma = 1 :=
      congrArg Prod.fst hsigma
    change (AlgEquiv.autCongr eE).symm
        (finiteIntermediateRestriction D E hEgal.to_normal sigma.1) = 1 at hfirst
    let rE := AlgEquiv.restrictNormalHom E sigma.1
    change (AlgEquiv.autCongr eE).symm rE = 1 at hfirst
    calc
      rE = (AlgEquiv.autCongr eE) ((AlgEquiv.autCongr eE).symm rE) :=
        ((AlgEquiv.autCongr eE).apply_symm_apply rE).symm
      _ = (AlgEquiv.autCongr eE) 1 := congrArg (AlgEquiv.autCongr eE) hfirst
      _ = 1 := map_one (AlgEquiv.autCongr eE)
  have hCione : AlgEquiv.restrictNormalHom C sigma.1 = 1 := by
    have hsecond : second sigma = 1 :=
      congrArg Prod.snd hsigma
    exact congrArg Subtype.val hsecond
  have hfix : ∀ o : Option (TRIndex D0 S),
      sigma.1 ∈ (familyD o).fixingSubgroup := by
    intro o
    cases o with
    | none =>
        change sigma.1 ∈ E.fixingSubgroup
        intro x
        calc
          sigma.1 (x : D) =
              ((AlgEquiv.restrictNormalHom E sigma.1) x : D) :=
            (@AlgEquiv.restrictNormalHom_apply ℚ inferInstance D
              inferInstance inferInstance E hEgal.to_normal sigma.1 x).symm
          _ = (x : D) :=
            congrArg Subtype.val (DFunLike.congr_fun hEone x)
    | some j =>
        let Cj := cyclotomicCubicCompositum
          D0 hD0three S j
        let hCjgal : IsGalois ℚ Cj :=
          tame_compositum_galois
            D0 hD0three S j
        letI : IsGalois ℚ Cj := hCjgal
        letI : Normal ℚ Cj := hCjgal.to_normal
        change sigma.1 ∈ Cj.fixingSubgroup
        by_cases hji : j = i
        · subst j
          intro x
          calc
            sigma.1 (x : D) =
                ((AlgEquiv.restrictNormalHom C sigma.1) x : D) :=
              (@AlgEquiv.restrictNormalHom_apply ℚ inferInstance D
                inferInstance inferInstance C hCgal.to_normal sigma.1 x).symm
            _ = (x : D) :=
              congrArg Subtype.val (DFunLike.congr_fun hCione x)
        · let eCj := tameCubicCompositum
              D0 hD0three S j
          let hCjfin : FiniteDimensional ℚ Cj :=
            tame_compositum_dimensional
              D0 hD0three S j
          have hprimeNe : i.prime ≠ j.prime := by
            intro h
            exact hji (TRIndex.prime_injective h.symm)
          have hunramified :
              letI : Algebra ℚ Cj := Cj.algebra'
              letI : FiniteDimensional ℚ Cj := hCjfin
              letI : NumberField Cj := NumberField.of_module_finite ℚ Cj
              RationalPrimeUnramified
                (S := NumberField.RingOfIntegers Cj) i.prime :=
            rational_unramified_alg eCj
              (rational_unramified_away
                j.prime j.prime_isPrime (j.prime_mod_eqone hD0three)
                i.prime_isPrime hprimeNe)
          have htrivial :=
            character_restriction_unramified
              Cj hCjfin hCjgal (MonoidHom.id Gal(Cj/ℚ))
                i.prime_isPrime hunramified P sigma
          have hres : AlgEquiv.restrictNormalHom Cj sigma.1 = 1 := by
            simpa using htrivial
          intro x
          calc
            sigma.1 (x : D) =
                ((AlgEquiv.restrictNormalHom Cj sigma.1) x : D) :=
              (@AlgEquiv.restrictNormalHom_apply ℚ inferInstance D
                inferInstance inferInstance Cj hCjgal.to_normal sigma.1 x).symm
            _ = (x : D) :=
              congrArg Subtype.val (DFunLike.congr_fun hres x)
  have hs : sigma.1 ∈
      (Finset.univ.sup familyD).fixingSubgroup := by
    have hs' : ∀ s : Finset (Option (TRIndex D0 S)),
        sigma.1 ∈ (s.sup familyD).fixingSubgroup := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
          rw [Finset.sup_insert, IntermediateField.fixingSubgroup_sup]
          exact ⟨hfix a, ih⟩
    exact hs' Finset.univ
  rw [compositum_sup_top,
    IntermediateField.fixingSubgroup_top, Subgroup.mem_bot] at hs
  exact Subtype.ext hs

/-- Restrict a faithful finite lift to one of the canonical ambient inertia
groups, with codomain narrowed to the kernel of its projected base map. -/
noncomputable def tameLiftInertia
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ)
    {A E : Type v} [Group A] [Group E]
    (pi : E →* A)
    (liftFinite : Gal(D0/ℚ) →* E)
    (hbaseInertia : ∀ i : TRIndex D0 S,
      ∀ sigma :
          (tameCyclotomicAbove D0 hD0three S i).inertia
            Gal(tameCorrectionCompositum D0 hD0three S/ℚ),
        pi (liftFinite
          (tameCyclotomicRestriction D0 hD0three S sigma.1)) = 1)
    (i : TRIndex D0 S) :
    (tameCyclotomicAbove D0 hD0three S i).inertia
        Gal(tameCorrectionCompositum D0 hD0three S/ℚ) →* pi.ker :=
  ((liftFinite.comp
      (tameCyclotomicRestriction D0 hD0three S)).comp
    ((tameCyclotomicAbove D0 hD0three S i).inertia
      Gal(tameCorrectionCompositum D0 hD0three S/ℚ)).subtype
  ).codRestrict pi.ker (hbaseInertia i)

/-- A finite product of independent correction characters cancels a lift on
every one of the indexed inertia subgroups. -/
theorem character_inertia_family
    {ι Γ A : Type*} [Fintype ι]
    [Group Γ] [CommGroup A]
    (I : ι → Subgroup Γ)
    (chi : ι → Γ →* A)
    (liftI : ∀ i, I i →* A)
    (hcancel : ∀ i (sigma : Γ) (hsigma : sigma ∈ I i),
      chi i sigma * liftI i ⟨sigma, hsigma⟩ = 1)
    (hcross : ∀ i j, i ≠ j →
      ∀ (sigma : Γ), sigma ∈ I j → chi i sigma = 1) :
    ∀ j (sigma : Γ) (hsigma : sigma ∈ I j),
      finiteCharacterProduct Finset.univ chi sigma *
        liftI j ⟨sigma, hsigma⟩ = 1 := by
  classical
  intro j sigma hsigma
  rw [character_product_single Finset.univ chi sigma j
    (Finset.mem_univ j)]
  · exact hcancel j sigma hsigma
  · intro i _ hij
    exact hcross i j hij sigma hsigma

set_option maxHeartbeats 2000000 in
-- The tame-pair construction unfolds intermediate-field inertia restrictions.
/-- The tame-pair construction with its finite intermediate-field character
retained, so unramifiedness of that field can later prove cross-prime
triviality of the inflated character. -/
theorem intermediate_cancels_pair
    (D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (C : IntermediateField ℚ D)
    (hCfin : letI : Algebra ℚ C := C.algebra'; FiniteDimensional ℚ C)
    (hCgal : letI : Algebra ℚ C := C.algebra'; IsGalois ℚ C)
    {q : ℕ} (hq : Nat.Prime q) (hqne : q ≠ 3)
    (P : Ideal (NumberField.RingOfIntegers D))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (hram :
      letI : Algebra ℚ C := C.algebra'
      letI : FiniteDimensional ℚ C := hCfin
      letI : NumberField C := NumberField.of_module_finite ℚ C
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q)
        (P.under (NumberField.RingOfIntegers C)) = 3)
    (hcard :
      letI : Algebra ℚ C := C.algebra'
      letI : FiniteDimensional ℚ C := hCfin
      Nat.card Gal(C/ℚ) = 3)
    {A G : Type*} [CommGroup A] [TopologicalSpace A]
    [DiscreteTopology A] [Group G]
    (liftI : P.inertia Gal(D/ℚ) →* A)
    (otherFinite : Gal(D/ℚ) →* G)
    (hother : ∀ sigma : P.inertia Gal(D/ℚ),
      otherFinite sigma.1 ^ 3 = 1)
    (hpair :
      letI : Algebra ℚ C := C.algebra'
      Function.Injective
        (((otherFinite.comp (P.inertia Gal(D/ℚ)).subtype).prod
          (numberInertiaRestriction C hCgal.to_normal q P)))) :
    ∃ chiC : letI : Algebra ℚ C := C.algebra'; Gal(C/ℚ) →* A,
      let chi := absoluteThroughIntermediate D C hCgal.to_normal chiC
      Continuous chi ∧
        ∀ (sigma : Gal(AlgebraicClosure ℚ/ℚ))
            (hsigma : AlgEquiv.restrictNormalHom D.toIntermediateField sigma ∈
              P.inertia Gal(D/ℚ)),
          chi sigma * liftI
            ⟨AlgEquiv.restrictNormalHom D.toIntermediateField sigma,
              hsigma⟩ = 1 := by
  letI : FiniteDimensional ℚ D := D.finiteDimensional
  letI : IsGalois ℚ D := D.isGalois
  letI : Normal ℚ D := D.isGalois.to_normal
  letI : Algebra ℚ C := C.algebra'
  letI : FiniteDimensional ℚ C := hCfin
  letI : IsGalois ℚ C := hCgal
  letI : NumberField C := NumberField.of_module_finite ℚ C
  let otherI : P.inertia Gal(D/ℚ) →* G :=
    otherFinite.comp (P.inertia Gal(D/ℚ)).subtype
  obtain ⟨chiC, hcancel⟩ :=
    cubic_cancels_pair
      C hCfin hCgal hq hqne P hram hcard liftI otherI
        (by exact hother) (by simpa [otherI] using hpair)
  refine ⟨chiC,
    absolute_through_continuous
      D C hCgal.to_normal chiC, ?_⟩
  intro sigma hsigma
  let tau : P.inertia Gal(D/ℚ) :=
    ⟨AlgEquiv.restrictNormalHom D.toIntermediateField sigma, hsigma⟩
  change chiC (finiteIntermediateRestriction D C hCgal.to_normal tau.1) *
      liftI tau = 1
  exact hcancel tau

set_option maxHeartbeats 4000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- Simultaneous correction builds and compares every finite character at once.
/-- Simultaneously choose the absolute cubic corrections supplied by the
tame-pair theorem and multiply them.  Unramifiedness of each cubic
intermediate field at the other indexed primes proves that the corrections
do not interfere with one another. -/
theorem cancels_tame_pairs
    {ι : Type u} [Finite ι]
    (D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (C : ι → IntermediateField ℚ D)
    (hCfin : ∀ i,
      letI : Algebra ℚ (C i) := (C i).algebra'
      FiniteDimensional ℚ (C i))
    (hCgal : ∀ i,
      letI : Algebra ℚ (C i) := (C i).algebra'
      IsGalois ℚ (C i))
    (q : ι → ℕ)
    (hq : ∀ i, Nat.Prime (q i))
    (hqne : ∀ i, q i ≠ 3)
    (hqmod : ∀ i, q i ≡ 1 [MOD 3])
    (hqinj : Function.Injective q)
    (eC : ∀ i,
      rationalCyclotomicCubic (q i) (hq i) (hqmod i) ≃ₐ[ℚ] C i)
    (P : ι → Ideal (NumberField.RingOfIntegers D))
    (hPprime : ∀ i, (P i).IsPrime)
    (hPlies : ∀ i, (P i).LiesOver (Ideal.rationalPrimeIdeal (q i)))
    (hram : ∀ i,
      letI : Algebra ℚ (C i) := (C i).algebra'
      letI : FiniteDimensional ℚ (C i) := hCfin i
      letI : NumberField (C i) := NumberField.of_module_finite ℚ (C i)
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal (q i))
        ((P i).under (NumberField.RingOfIntegers (C i))) = 3)
    (hcard : ∀ i,
      letI : Algebra ℚ (C i) := (C i).algebra'
      letI : FiniteDimensional ℚ (C i) := hCfin i
      Nat.card Gal(C i/ℚ) = 3)
    {A G : Type v} [CommGroup A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalGroup A] [Group G]
    (liftI : ∀ i, (P i).inertia Gal(D/ℚ) →* A)
    (otherFinite : Gal(D/ℚ) →* G)
    (hother : ∀ i (sigma : (P i).inertia Gal(D/ℚ)),
      otherFinite sigma.1 ^ 3 = 1)
    (hpair : ∀ i,
      letI : Algebra ℚ (C i) := (C i).algebra'
      Function.Injective
        (((otherFinite.comp ((P i).inertia Gal(D/ℚ)).subtype).prod
          (numberInertiaRestriction
            (C i) (hCgal i).to_normal (q i) (P i))))) :
    ∃ chi : Gal(AlgebraicClosure ℚ/ℚ) →* A,
      Continuous chi ∧
        (∀ i (sigma : Gal(AlgebraicClosure ℚ/ℚ))
            (hsigma :
              AlgEquiv.restrictNormalHom D.toIntermediateField sigma ∈
                (P i).inertia Gal(D/ℚ)),
          chi sigma * liftI i
            ⟨AlgEquiv.restrictNormalHom D.toIntermediateField sigma,
              hsigma⟩ = 1) ∧
        ∀ (P3 : Ideal (NumberField.RingOfIntegers D)),
          P3.IsPrime →
          P3.LiesOver (Ideal.rationalPrimeIdeal 3) →
          ∀ (sigma : Gal(AlgebraicClosure ℚ/ℚ))
            (_hsigma :
              AlgEquiv.restrictNormalHom D.toIntermediateField sigma ∈
                P3.inertia Gal(D/ℚ)),
            chi sigma = 1 := by
  classical
  letI := Fintype.ofFinite ι
  letI (i : ι) : (P i).IsPrime := hPprime i
  letI (i : ι) : (P i).LiesOver
      (Ideal.rationalPrimeIdeal (q i)) := hPlies i
  have hexists (i : ι) :
      ∃ chiC : letI : Algebra ℚ (C i) := (C i).algebra';
          Gal(C i/ℚ) →* A,
        let chi := absoluteThroughIntermediate
          D (C i) (hCgal i).to_normal chiC
        Continuous chi ∧
          ∀ (sigma : Gal(AlgebraicClosure ℚ/ℚ))
              (hsigma :
                AlgEquiv.restrictNormalHom D.toIntermediateField sigma ∈
                  (P i).inertia Gal(D/ℚ)),
            chi sigma * liftI i
              ⟨AlgEquiv.restrictNormalHom D.toIntermediateField sigma,
                hsigma⟩ = 1 :=
    intermediate_cancels_pair
      D (C i) (hCfin i) (hCgal i) (hq i) (hqne i) (P i)
        (hram i) (hcard i) (liftI i) otherFinite (hother i) (hpair i)
  choose chiC hchiContinuous hchiCancel using hexists
  let chi : ι → Gal(AlgebraicClosure ℚ/ℚ) →* A := fun i =>
    absoluteThroughIntermediate
      D (C i) (hCgal i).to_normal (chiC i)
  let total : Gal(AlgebraicClosure ℚ/ℚ) →* A :=
    finiteCharacterProduct Finset.univ chi
  refine ⟨total,
    character_product_continuous Finset.univ chi
      (fun i _ => hchiContinuous i), ?_, ?_⟩
  · let I : ι → Subgroup Gal(AlgebraicClosure ℚ/ℚ) := fun i =>
      Subgroup.comap
        (AlgEquiv.restrictNormalHom D.toIntermediateField)
        ((P i).inertia Gal(D/ℚ))
    let restrictI : ∀ i, I i →* (P i).inertia Gal(D/ℚ) := fun i =>
      { toFun := fun sigma =>
          ⟨AlgEquiv.restrictNormalHom D.toIntermediateField sigma.1,
            sigma.2⟩
        map_one' := by
          apply Subtype.ext
          exact map_one (AlgEquiv.restrictNormalHom D.toIntermediateField)
        map_mul' := by
          intro sigma tau
          apply Subtype.ext
          exact map_mul (AlgEquiv.restrictNormalHom D.toIntermediateField)
            sigma.1 tau.1 }
    have hcross' : ∀ i j, i ≠ j →
        ∀ (sigma : Gal(AlgebraicClosure ℚ/ℚ)),
          sigma ∈ I j → chi i sigma = 1 := by
      intro i j hij sigma hsigma
      have hqji : q j ≠ q i := by
        intro h
        exact hij (hqinj h).symm
      have hunramified :
          letI : Algebra ℚ (C i) := (C i).algebra'
          letI : FiniteDimensional ℚ (C i) := hCfin i
          letI : NumberField (C i) := NumberField.of_module_finite ℚ (C i)
          RationalPrimeUnramified
            (S := NumberField.RingOfIntegers (C i)) (q j) :=
        rational_unramified_alg (eC i)
          (rational_unramified_away
            (q i) (hq i) (hqmod i) (hq j) hqji)
      exact absolute_through_intermediate
        D (C i) (hCfin i) (hCgal i) (chiC i) (hq j)
          hunramified (P j) sigma hsigma
    intro i sigma hsigma
    exact character_inertia_family
      I chi
        (fun i => (liftI i).comp (restrictI i))
        (fun i sigma hsigma => hchiCancel i sigma hsigma)
        hcross' i sigma hsigma
  · intro P3 hP3prime hP3lies sigma hsigma
    letI : P3.IsPrime := hP3prime
    letI : P3.LiesOver (Ideal.rationalPrimeIdeal 3) := hP3lies
    rw [finite_character_product]
    apply Finset.prod_eq_one
    intro i _
    have hunramified :
        letI : Algebra ℚ (C i) := (C i).algebra'
        letI : FiniteDimensional ℚ (C i) := hCfin i
        letI : NumberField (C i) := NumberField.of_module_finite ℚ (C i)
        RationalPrimeUnramified
          (S := NumberField.RingOfIntegers (C i)) 3 :=
      rational_unramified_alg (eC i)
        (rational_unramified_away
          (q i) (hq i) (hqmod i) Nat.prime_three (hqne i).symm)
    exact absolute_through_intermediate
      D (C i) (hCfin i) (hCgal i) (chiC i) Nat.prime_three
        hunramified P3 sigma hsigma

set_option maxHeartbeats 4000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- The indexed correction product synthesizes all common-compositum fields.
/-- Apply the finite cyclotomic cleanup to exactly the rational primes outside
`S`, distinct from `3`, that ramify in a fixed finite Galois `3`-extension
`D0`.  The ambient field `D` is allowed to be a larger finite Galois field
containing both the lift field and all the cubic cyclotomic correction fields.

The remaining hypotheses are local data in that common ambient field; no
extra cross-prime independence assumption is needed. -/
theorem tame_ramified_product
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ)
    (D : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (C : TRIndex D0 S → IntermediateField ℚ D)
    (hCfin : ∀ i,
      letI : Algebra ℚ (C i) := (C i).algebra'
      FiniteDimensional ℚ (C i))
    (hCgal : ∀ i,
      letI : Algebra ℚ (C i) := (C i).algebra'
      IsGalois ℚ (C i))
    (eC : ∀ i,
      rationalCyclotomicCubic i.prime i.prime_isPrime
          (i.prime_mod_eqone hD0three) ≃ₐ[ℚ] C i)
    (P : TRIndex D0 S →
      Ideal (NumberField.RingOfIntegers D))
    (hPprime : ∀ i, (P i).IsPrime)
    (hPlies : ∀ i,
      (P i).LiesOver (Ideal.rationalPrimeIdeal i.prime))
    (hram : ∀ i,
      letI : Algebra ℚ (C i) := (C i).algebra'
      letI : FiniteDimensional ℚ (C i) := hCfin i
      letI : NumberField (C i) := NumberField.of_module_finite ℚ (C i)
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal i.prime)
        ((P i).under (NumberField.RingOfIntegers (C i))) = 3)
    (hcard : ∀ i,
      letI : Algebra ℚ (C i) := (C i).algebra'
      letI : FiniteDimensional ℚ (C i) := hCfin i
      Nat.card Gal(C i/ℚ) = 3)
    {A G : Type v} [CommGroup A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalGroup A] [Group G]
    (liftI : ∀ i, (P i).inertia Gal(D/ℚ) →* A)
    (otherFinite : Gal(D/ℚ) →* G)
    (hother : ∀ i (sigma : (P i).inertia Gal(D/ℚ)),
      otherFinite sigma.1 ^ 3 = 1)
    (hpair : ∀ i,
      letI : Algebra ℚ (C i) := (C i).algebra'
      Function.Injective
        (((otherFinite.comp ((P i).inertia Gal(D/ℚ)).subtype).prod
          (numberInertiaRestriction
            (C i) (hCgal i).to_normal i.prime (P i))))) :
    ∃ chi : Gal(AlgebraicClosure ℚ/ℚ) →* A,
      Continuous chi ∧
        (∀ i (sigma : Gal(AlgebraicClosure ℚ/ℚ))
            (hsigma :
              AlgEquiv.restrictNormalHom D.toIntermediateField sigma ∈
                (P i).inertia Gal(D/ℚ)),
          chi sigma * liftI i
            ⟨AlgEquiv.restrictNormalHom D.toIntermediateField sigma,
              hsigma⟩ = 1) ∧
        ∀ (P3 : Ideal (NumberField.RingOfIntegers D)),
          P3.IsPrime →
          P3.LiesOver (Ideal.rationalPrimeIdeal 3) →
          ∀ (sigma : Gal(AlgebraicClosure ℚ/ℚ))
            (_hsigma :
              AlgEquiv.restrictNormalHom D.toIntermediateField sigma ∈
                P3.inertia Gal(D/ℚ)),
            chi sigma = 1 := by
  apply cancels_tame_pairs
    D C hCfin hCgal
      (fun i => i.prime)
      (fun i => i.prime_isPrime)
      (fun i => i.prime_ne_three)
      (fun i => i.prime_mod_eqone hD0three)
      TRIndex.prime_injective
      eC P hPprime hPlies hram hcard liftI otherFinite hother hpair

set_option maxHeartbeats 4000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- Canonical field construction expands the full indexed correction family.
/-- The tame correction product in the canonical common compositum.  Unlike
`tame_ramified_product`, this statement has no ambient
field, cubic-field, upper-prime, ramification-index, or degree hypotheses:
all of those objects are constructed from `D0` and verified internally.

The remaining `liftI`, `hother`, and `hpair` arguments are the actual local
character supplied by the preliminary lift and its joint-faithfulness with
the cyclotomic restriction. -/
theorem canonical_tame_ramified
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ)
    {A G : Type v} [CommGroup A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalGroup A] [Group G]
    (liftI : ∀ i : TRIndex D0 S,
      let D := tameCorrectionCompositum D0 hD0three S
      let P := tameCyclotomicAbove D0 hD0three S i
      P.inertia Gal(D/ℚ) →* A)
    (otherFinite :
      Gal(tameCorrectionCompositum D0 hD0three S/ℚ) →* G)
    (hother : ∀ i (sigma :
        (tameCyclotomicAbove D0 hD0three S i).inertia
          Gal(tameCorrectionCompositum D0 hD0three S/ℚ)),
      otherFinite sigma.1 ^ 3 = 1)
    (hpair : ∀ i,
      let D := tameCorrectionCompositum D0 hD0three S
      let C := cyclotomicCubicCompositum D0 hD0three S i
      let P := tameCyclotomicAbove D0 hD0three S i
      letI : Algebra ℚ C := C.algebra'
      let hCgal : IsGalois ℚ C :=
        tame_compositum_galois
          D0 hD0three S i
      letI : P.IsPrime :=
        tame_cyclotomic_above D0 hD0three S i
      letI : P.LiesOver (Ideal.rationalPrimeIdeal i.prime) :=
        tame_above_lies D0 hD0three S i
      Function.Injective
        (((otherFinite.comp (P.inertia Gal(D/ℚ)).subtype).prod
          (numberInertiaRestriction C
            hCgal.to_normal i.prime P)))) :
    ∃ chi : Gal(AlgebraicClosure ℚ/ℚ) →* A,
      Continuous chi ∧
        (∀ i (sigma : Gal(AlgebraicClosure ℚ/ℚ))
            (hsigma :
              AlgEquiv.restrictNormalHom
                  (tameCorrectionCompositum
                    D0 hD0three S).toIntermediateField sigma ∈
                (tameCyclotomicAbove
                  D0 hD0three S i).inertia
                    Gal(tameCorrectionCompositum
                      D0 hD0three S/ℚ)),
          chi sigma * liftI i
            ⟨AlgEquiv.restrictNormalHom
              (tameCorrectionCompositum
                D0 hD0three S).toIntermediateField sigma, hsigma⟩ = 1) ∧
        ∀ (P3 : Ideal (NumberField.RingOfIntegers
            (tameCorrectionCompositum D0 hD0three S))),
          P3.IsPrime →
          P3.LiesOver (Ideal.rationalPrimeIdeal 3) →
          ∀ (sigma : Gal(AlgebraicClosure ℚ/ℚ))
            (_hsigma :
              AlgEquiv.restrictNormalHom
                  (tameCorrectionCompositum
                    D0 hD0three S).toIntermediateField sigma ∈
                P3.inertia
                  Gal(tameCorrectionCompositum
                    D0 hD0three S/ℚ)),
            chi sigma = 1 := by
  let D := tameCorrectionCompositum D0 hD0three S
  let C : TRIndex D0 S → IntermediateField ℚ D :=
    cyclotomicCubicCompositum D0 hD0three S
  let P : TRIndex D0 S →
      Ideal (NumberField.RingOfIntegers D) :=
    tameCyclotomicAbove D0 hD0three S
  let hCfin : ∀ i,
      letI : Algebra ℚ (C i) := (C i).algebra'
      FiniteDimensional ℚ (C i) := fun i =>
    tame_compositum_dimensional
      D0 hD0three S i
  let hCgal : ∀ i,
      letI : Algebra ℚ (C i) := (C i).algebra'
      IsGalois ℚ (C i) := fun i =>
    tame_compositum_galois
      D0 hD0three S i
  exact tame_ramified_product
    (A := A) (G := G)
    D0 hD0three S D C hCfin hCgal
    (tameCubicCompositum D0 hD0three S)
    P
    (tame_cyclotomic_above D0 hD0three S)
    (tame_above_lies D0 hD0three S)
    (tame_compositum_idx
      D0 hD0three S)
    (tame_compositum_card D0 hD0three S)
    liftI otherFinite hother hpair

set_option maxHeartbeats 4000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 500000 in
-- Joint faithfulness unfolds both finite restrictions and inertia structures.
/-- The canonical tame correction attached to a faithful finite lift.

The caller only has to show that the projected finite lift kills the relevant
inertia groups.  The order-three condition for restriction to the lift field
and the joint-faithfulness hypothesis used by the local tame-pair theorem are
then automatic. -/
theorem canonical_tame_lift
    (D0 : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hD0three : IsPGroup 3 Gal(D0/ℚ))
    (S : Finset ℕ)
    {A E : Type v} [Group A] [Group E]
    [TopologicalSpace E] [DiscreteTopology E] [IsTopologicalGroup E]
    (pi : E →* A)
    (hcentral : pi.ker ≤ Subgroup.center E)
    (liftFinite : Gal(D0/ℚ) →* E)
    (hliftFinite : Function.Injective liftFinite)
    (hkernelCube : ∀ z : pi.ker, z ^ 3 = 1)
    (hbaseInertia : ∀ i : TRIndex D0 S,
      ∀ sigma :
          (tameCyclotomicAbove D0 hD0three S i).inertia
            Gal(tameCorrectionCompositum D0 hD0three S/ℚ),
        pi (liftFinite
          (tameCyclotomicRestriction D0 hD0three S sigma.1)) = 1) :
    let liftI := tameLiftInertia
      D0 hD0three S pi liftFinite hbaseInertia
    ∃ chi : Gal(AlgebraicClosure ℚ/ℚ) →* pi.ker,
      Continuous chi ∧
        (∀ i (sigma : Gal(AlgebraicClosure ℚ/ℚ))
            (hsigma :
              AlgEquiv.restrictNormalHom
                  (tameCorrectionCompositum
                    D0 hD0three S).toIntermediateField sigma ∈
                (tameCyclotomicAbove
                  D0 hD0three S i).inertia
                    Gal(tameCorrectionCompositum
                      D0 hD0three S/ℚ)),
          chi sigma * liftI i
            ⟨AlgEquiv.restrictNormalHom
              (tameCorrectionCompositum
                D0 hD0three S).toIntermediateField sigma, hsigma⟩ = 1) ∧
        ∀ (P3 : Ideal (NumberField.RingOfIntegers
            (tameCorrectionCompositum D0 hD0three S))),
          P3.IsPrime →
          P3.LiesOver (Ideal.rationalPrimeIdeal 3) →
          ∀ (sigma : Gal(AlgebraicClosure ℚ/ℚ))
            (_hsigma :
              AlgEquiv.restrictNormalHom
                  (tameCorrectionCompositum
                    D0 hD0three S).toIntermediateField sigma ∈
                P3.inertia
                  Gal(tameCorrectionCompositum
                    D0 hD0three S/ℚ)),
            chi sigma = 1 := by
  dsimp only
  letI : CommGroup pi.ker :=
    centralExtensionComm pi hcentral
  let liftI := tameLiftInertia
    D0 hD0three S pi liftFinite hbaseInertia
  apply canonical_tame_ramified
    D0 hD0three S liftI
      (liftFinite.comp
        (tameCyclotomicRestriction D0 hD0three S))
  · intro i sigma
    have hcube := congrArg Subtype.val (hkernelCube (liftI i sigma))
    simpa [liftI, tameLiftInertia] using hcube
  · intro i
    dsimp only
    intro sigma tau h
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    apply tame_restriction_injective D0 hD0three S i
    apply Prod.ext
    · apply hliftFinite
      exact hfst
    · exact hsnd

/-- If a corrected finite homomorphism kills every inertia subgroup outside
`S`, the field fixed by its kernel is unramified outside `S`. -/
theorem outside_inertia_killed
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (S : Finset ℕ) {E : Type*} [Group E]
    (corrected : Gal(K/ℚ) →* E)
    (hkill :
      ∀ (q : ℕ) (_hq : Nat.Prime q), q ∉ S →
        ∀ (P : Ideal (NumberField.RingOfIntegers K)),
          P.IsPrime → P.LiesOver (Ideal.rationalPrimeIdeal q) →
            ∀ sigma : P.inertia Gal(K/ℚ), corrected sigma.1 = 1) :
    let H := corrected.ker
    let F := IntermediateField.fixedField H
    letI : Algebra ℚ F := F.algebra'
    letI : FiniteDimensional ℚ F := inferInstance
    letI : NumberField F := NumberField.of_module_finite ℚ F
    UnramifiedOutside F S := by
  let H : Subgroup Gal(K/ℚ) := corrected.ker
  letI : H.Normal := by
    dsimp only [H]
    infer_instance
  apply fixed_outside_inertia K S H
  intro q hq hqS P hP hPover sigma hsigma
  exact hkill q hq hqS P hP hPover ⟨sigma, hsigma⟩

end TBluepr
end Towers
