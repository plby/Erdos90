import Towers.NumberTheory.TameDiscriminant
import Towers.Group.PGroup
import Towers.Group.Metacyclic


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Towers

lemma galois_group_cyclic
    {k K : Type*} [Field k] [Field K] [Finite K] [Algebra k K] :
    IsCyclic (Gal(K/k)) := by
  classical
  have hFiniteTop : Finite K := inferInstance
  letI : Finite K := hFiniteTop
  exact inferInstance

lemma number_above_maximal
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    P.IsMaximal := by
  have hp_ne_bot : Ideal.rationalPrimeIdeal q ≠ ⊥ :=
    rational_ne_bot hq
  have hP_ne_bot : P ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hp_ne_bot P
  exact Ring.DimensionLEOne.maximalOfPrime hP_ne_bot inferInstance

lemma number_residue_cyclic
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    IsCyclic (NumberField.RingOfIntegers L ⧸ P)ˣ := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  letI : Field (NumberField.RingOfIntegers L ⧸ P) :=
    Ideal.Quotient.field P
  have hFiniteResidue :
      Finite (NumberField.RingOfIntegers L ⧸ P) :=
    inferInstance
  letI : Finite (NumberField.RingOfIntegers L ⧸ P) :=
    hFiniteResidue
  exact inferInstance

lemma cyclic_injective_units
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    {Γ : Type*} [Group Γ]
    (χ : Γ →* (NumberField.RingOfIntegers L ⧸ P)ˣ)
    (hχ : Function.Injective χ) :
    IsCyclic Γ := by
  classical
  have hUnits :
      IsCyclic (NumberField.RingOfIntegers L ⧸ P)ˣ :=
    number_residue_cyclic (L := L) hq P
  letI : IsCyclic (NumberField.RingOfIntegers L ⧸ P)ˣ :=
    hUnits
  exact isCyclic_of_injective χ hχ

lemma inertia_ramification_idx
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    Nat.card (P.inertia (Gal(L/ℚ))) =
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P := by
  classical
  let p : Ideal ℤ := Ideal.rationalPrimeIdeal q
  letI : p.IsPrime := by
    simpa [p] using rational_prime_ideal hq
  letI : P.LiesOver p := by
    simpa [p] using (inferInstance : P.LiesOver (Ideal.rationalPrimeIdeal q))
  have hp_ne_bot : p ≠ ⊥ := by
    simpa [p] using rational_ne_bot hq
  letI : p.IsMaximal := by
    simpa [p] using rational_ideal_maximal hq
  letI : P.IsMaximal := by
    simpa [p] using
      number_above_maximal (L := L) hq P
  letI : Field (ℤ ⧸ p) := Ideal.Quotient.field p
  letI : Field (NumberField.RingOfIntegers L ⧸ P) :=
    Ideal.Quotient.field P
  have hBaseFinite : Finite (ℤ ⧸ p) :=
    Ring.HasFiniteQuotients.finiteQuotient hp_ne_bot
  letI : Finite (ℤ ⧸ p) := hBaseFinite
  letI : PerfectField (ℤ ⧸ p) := PerfectField.ofFinite
  have hResidueFinite :
      Finite (NumberField.RingOfIntegers L ⧸ P) :=
    inferInstance
  letI : Finite (NumberField.RingOfIntegers L ⧸ P) :=
    hResidueFinite
  letI : Module.Finite (ℤ ⧸ p) (NumberField.RingOfIntegers L ⧸ P) :=
    Module.Finite.of_finite
  letI : Algebra.IsSeparable (ℤ ⧸ p)
      (NumberField.RingOfIntegers L ⧸ P) :=
    inferInstance
  letI : Finite (Gal(L/ℚ)) :=
    IsGaloisGroup.finite (Gal(L/ℚ)) ℚ L
  letI : IsGaloisGroup (Gal(L/ℚ)) ℤ (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing
      (Gal(L/ℚ)) ℤ (NumberField.RingOfIntegers L) ℚ L
  have hCard :
      Nat.card (P.inertia (Gal(L/ℚ))) =
        Ideal.ramificationIdxIn p (NumberField.RingOfIntegers L) :=
    Ideal.card_inertia_eq_ramificationIdxIn p hp_ne_bot P
  have hIdx :
      Ideal.ramificationIdxIn p (NumberField.RingOfIntegers L) =
        Ideal.ramificationIdx p P :=
    Ideal.ramificationIdxIn_eq_ramificationIdx p P (Gal(L/ℚ))
  simpa [p] using hCard.trans hIdx

lemma tame_inertia_coprime
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (hTame : RationalTamePrimes
      (S := NumberField.RingOfIntegers L) q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    Nat.Coprime q (Nat.card (P.inertia (Gal(L/ℚ)))) := by
  classical
  have hP_mem :
      P ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal q)
        (NumberField.RingOfIntegers L) :=
    ⟨inferInstance, inferInstance⟩
  have hRamificationCoprime :
      Nat.Coprime q
        (Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P) :=
    hTame P hP_mem
  have hCard :
      Nat.card (P.inertia (Gal(L/ℚ))) =
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P :=
    inertia_ramification_idx (L := L) hq P
  rw [hCard]
  exact hRamificationCoprime

noncomputable def idealResidueMaximal
    {R : Type*} [CommRing R]
    (I : Ideal R) [I.IsPrime] [I.IsMaximal] :
    R ⧸ I ≃+* I.ResidueField :=
  RingEquiv.ofBijective
    (algebraMap (R ⧸ I) I.ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField I)

noncomputable def unitsResidueMaximal
    {R : Type*} [CommRing R]
    (I : Ideal R) [I.IsPrime] [I.IsMaximal] :
    (R ⧸ I)ˣ ≃* I.ResidueFieldˣ :=
  Units.mapEquiv (idealResidueMaximal I).toMulEquiv

@[simp]
lemma units_residue_maximal
    {R : Type*} [CommRing R]
    (I : Ideal R) [I.IsPrime] [I.IsMaximal]
    (u : (R ⧸ I)ˣ) :
    (unitsResidueMaximal I u : I.ResidueField) =
      algebraMap (R ⧸ I) I.ResidueField u := by
  rfl

lemma number_char_p
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    CharP P.ResidueField q := by
  classical
  have hq_mem_base :
      (q : ℤ) ∈ Ideal.rationalPrimeIdeal q := by
    exact Ideal.subset_span (by simp)
  have hq_mem_P :
      algebraMap ℤ (NumberField.RingOfIntegers L) (q : ℤ) ∈ P := by
    exact
      (Ideal.mem_of_liesOver
        (B := NumberField.RingOfIntegers L)
        (p := Ideal.rationalPrimeIdeal q)
        (P := P)
        (x := (q : ℤ))).mp hq_mem_base
  have hq_zero_alg :
      algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (algebraMap ℤ (NumberField.RingOfIntegers L) (q : ℤ)) = 0 := by
    rw [Ideal.algebraMap_residueField_eq_zero]
    exact hq_mem_P
  have hq_zero : (q : P.ResidueField) = 0 := by
    simpa [Int.cast_natCast,
      IsScalarTower.algebraMap_apply ℤ
        (NumberField.RingOfIntegers L) P.ResidueField] using hq_zero_alg
  exact (CharP.charP_iff_prime_eq_zero hq).mpr hq_zero

lemma number_local_residue
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    Finite P.ResidueField := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  have hQuotFinite :
      Finite (NumberField.RingOfIntegers L ⧸ P) :=
    inferInstance
  letI : Finite (NumberField.RingOfIntegers L ⧸ P) :=
    hQuotFinite
  exact
    Finite.of_equiv
      (NumberField.RingOfIntegers L ⧸ P)
      (idealResidueMaximal P).toEquiv

lemma number_units_cyclic
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    IsCyclic P.ResidueFieldˣ := by
  classical
  have hResidueFinite :
      Finite P.ResidueField :=
    number_local_residue (L := L) hq P
  letI : Finite P.ResidueField :=
    hResidueFinite
  exact inferInstance

lemma cyclic_residue_units
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    {Γ : Type*} [Group Γ]
    (χ : Γ →* P.ResidueFieldˣ)
    (hχ : Function.Injective χ) :
    IsCyclic Γ := by
  classical
  have hUnits :
      IsCyclic P.ResidueFieldˣ :=
    number_units_cyclic (L := L) hq P
  letI : IsCyclic P.ResidueFieldˣ :=
    hUnits
  exact isCyclic_of_injective χ hχ

lemma cyclic_character_sylow
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (hCardCoprime : Nat.Coprime q (Nat.card (P.inertia (Gal(L/ℚ)))))
    (S : Sylow q (P.inertia (Gal(L/ℚ))))
    (χ : P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ)
    (hKer : χ.ker ≤ (S : Subgroup (P.inertia (Gal(L/ℚ))))) :
    IsCyclic (P.inertia (Gal(L/ℚ))) := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  have hχ :
      Function.Injective χ := by
    exact
      monoid_sylow_coprime
        χ S hKer hCardCoprime
  exact
    cyclic_residue_units
      (L := L) hq P χ hχ

lemma ideal_sub
    {R : Type*} [CommRing R] (I : Ideal R) {x y : R}
    (hxy : x - y ∈ I) :
    Ideal.Quotient.mk I x = Ideal.Quotient.mk I y := by
  have hquot :
      Ideal.Quotient.mk I x = Ideal.Quotient.mk I y ↔ x - y ∈ I := by
    exact Ideal.Quotient.eq
  exact hquot.2 hxy

lemma ideal_quotient_sub
    {R : Type*} [CommRing R] (I : Ideal R) {x y : R} :
    Ideal.Quotient.mk I x = Ideal.Quotient.mk I y ↔ x - y ∈ I := by
  have hquot :
      Ideal.Quotient.mk I x = Ideal.Quotient.mk I y ↔ x - y ∈ I := by
    exact Ideal.Quotient.eq
  exact hquot

lemma residue_field_sub
    {R : Type*} [CommRing R] {I : Ideal R} [I.IsPrime] {x y : R}
    (hxy : x - y ∈ I) :
    algebraMap R I.ResidueField x = algebraMap R I.ResidueField y := by
  have hzero :
      algebraMap R I.ResidueField (x - y) = 0 := by
    exact (Ideal.algebraMap_residueField_eq_zero (I := I)).2 hxy
  have hsub :
      algebraMap R I.ResidueField x - algebraMap R I.ResidueField y = 0 := by
    simpa [map_sub] using hzero
  exact sub_eq_zero.mp hsub

lemma ideal_residue_sub
    {R : Type*} [CommRing R] {I : Ideal R} [I.IsPrime] {x y : R} :
    algebraMap R I.ResidueField x = algebraMap R I.ResidueField y ↔ x - y ∈ I := by
  constructor
  · intro hxy
    have hzero :
        algebraMap R I.ResidueField (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    exact (Ideal.algebraMap_residueField_eq_zero (I := I)).1 hzero
  · intro hxy
    exact residue_field_sub (I := I) hxy

lemma number_card_int
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ}
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    Nat.card (ℤ ⧸ P.under ℤ) = q := by
  have hp_eq :
      Ideal.rationalPrimeIdeal q = P.under ℤ :=
    Ideal.LiesOver.over (P := P) (p := Ideal.rationalPrimeIdeal q)
  rw [← hp_eq]
  exact Int.card_ideal_quot q

lemma arith_frob_mk
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ}
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : Gal(L/ℚ)) (hσ : IsArithFrobAt ℤ σ P)
    (x : NumberField.RingOfIntegers L) :
    Ideal.Quotient.mk P (σ • x) =
      (Ideal.Quotient.mk P x) ^ q := by
  have hcard :
      Nat.card (ℤ ⧸ P.under ℤ) = q :=
    number_card_int (L := L) P
  rw [← map_pow, Ideal.Quotient.eq]
  simpa [hcard] using hσ x

lemma number_arith_frob
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ}
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : Gal(L/ℚ)) (hσ : IsArithFrobAt ℤ σ P)
    (x : NumberField.RingOfIntegers L) :
    algebraMap (NumberField.RingOfIntegers L) P.ResidueField (σ • x) =
      (algebraMap (NumberField.RingOfIntegers L) P.ResidueField x) ^ q := by
  have hcard :
      Nat.card (ℤ ⧸ P.under ℤ) = q :=
    number_card_int (L := L) P
  rw [← map_pow]
  exact residue_field_sub (I := P) (by simpa [hcard] using hσ x)

lemma number_smul_sub
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (x : NumberField.RingOfIntegers L) :
    ((σ : Gal(L/ℚ)) • x) - x ∈ P := by
  have hσ :
      (σ : Gal(L/ℚ)) ∈ P.inertia (Gal(L/ℚ)) := by
    exact σ.property
  exact hσ x

lemma number_mk_smul
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (x : NumberField.RingOfIntegers L) :
    Ideal.Quotient.mk P (((σ : Gal(L/ℚ)) • x)) =
      Ideal.Quotient.mk P x := by
  have hcong :
      ((σ : Gal(L/ℚ)) • x) - x ∈ P := by
    exact number_smul_sub (L := L) P σ x
  exact ideal_sub P hcong

lemma number_residue_smul
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) [P.IsPrime]
    (σ : P.inertia (Gal(L/ℚ))) (x : NumberField.RingOfIntegers L) :
    algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (((σ : Gal(L/ℚ)) • x)) =
      algebraMap (NumberField.RingOfIntegers L) P.ResidueField x := by
  have hcong :
      ((σ : Gal(L/ℚ)) • x) - x ∈ P := by
    exact number_smul_sub (L := L) P σ x
  exact residue_field_sub (I := P) hcong

lemma field_inertia_stabilizer
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) :
    (σ : Gal(L/ℚ)) ∈ MulAction.stabilizer (Gal(L/ℚ)) P := by
  have hσ :
      (σ : Gal(L/ℚ)) ∈ P.inertia (Gal(L/ℚ)) := by
    exact σ.property
  exact (Ideal.inertia_le_stabilizer (M := Gal(L/ℚ)) P) hσ

lemma number_smul_prime
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) {x : NumberField.RingOfIntegers L}
    (hx : x ∈ P) :
    ((σ : Gal(L/ℚ)) • x) ∈ P := by
  classical
  have hStab :
      (σ : Gal(L/ℚ)) • P = P := by
    exact field_inertia_stabilizer (L := L) P σ
  have hMem :
      ((σ : Gal(L/ℚ)) • x) ∈ (σ : Gal(L/ℚ)) • P := by
    exact Ideal.smul_mem_pointwise_smul (σ : Gal(L/ℚ)) x P hx
  simpa [hStab] using hMem

lemma number_inertia_stabilizer
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : P.inertia (Gal(L/ℚ))) :
    Ideal.Quotient.stabilizerHom P (Ideal.rationalPrimeIdeal q) (Gal(L/ℚ))
        ⟨(σ : Gal(L/ℚ)), field_inertia_stabilizer (L := L) P σ⟩ = 1 := by
  classical
  apply MonoidHom.mem_ker.mp
  rw [Ideal.Quotient.ker_stabilizerHom]
  change (σ : Gal(L/ℚ)) ∈ P.inertia (Gal(L/ℚ))
  exact σ.property

lemma number_inertia_sq
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) {x : NumberField.RingOfIntegers L}
    (hx : x ∈ P ^ 2) :
    ((σ : Gal(L/ℚ)) • x) ∈ P ^ 2 := by
  classical
  have hStab :
      (σ : Gal(L/ℚ)) • P = P := by
    exact field_inertia_stabilizer (L := L) P σ
  have hPow :
      (σ : Gal(L/ℚ)) • (P ^ 2) = P ^ 2 := by
    calc
      (σ : Gal(L/ℚ)) • (P ^ 2) =
          ((σ : Gal(L/ℚ)) • P) ^ 2 := by
        simp [pow_two]
      _ = P ^ 2 := by
        rw [hStab]
  have hMem :
      ((σ : Gal(L/ℚ)) • x) ∈ (σ : Gal(L/ℚ)) • (P ^ 2) := by
    exact Ideal.smul_mem_pointwise_smul (σ : Gal(L/ℚ)) x (P ^ 2) hx
  simpa [hPow] using hMem

lemma smul_prime_sq
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) :
    (σ : Gal(L/ℚ)) • (P ^ 2) = P ^ 2 := by
  classical
  have hStab :
      (σ : Gal(L/ℚ)) • P = P := by
    exact field_inertia_stabilizer (L := L) P σ
  calc
    (σ : Gal(L/ℚ)) • (P ^ 2) =
        ((σ : Gal(L/ℚ)) • P) ^ 2 := by
      simp [pow_two]
    _ = P ^ 2 := by
      rw [hStab]

lemma number_field_sq
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) :
    P ^ 2 =
      (P ^ 2).map
        ((MulSemiringAction.toRingEquiv (Gal(L/ℚ))
          (NumberField.RingOfIntegers L) (σ : Gal(L/ℚ))) :
            NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) := by
  have hPow :
      (σ : Gal(L/ℚ)) • (P ^ 2) = P ^ 2 := by
    exact smul_prime_sq (L := L) P σ
  change P ^ 2 =
    (P ^ 2).map
      (MulSemiringAction.toRingHom (Gal(L/ℚ))
        (NumberField.RingOfIntegers L) (σ : Gal(L/ℚ)))
  rw [Ideal.map_pow]
  simpa [Ideal.pointwise_smul_def] using hPow.symm

noncomputable def number_wild_subgroup
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) :
    Subgroup (P.inertia (Gal(L/ℚ))) where
  carrier :=
    {σ | ∀ x : NumberField.RingOfIntegers L,
      ((σ : Gal(L/ℚ)) • x) - x ∈ P ^ 2}
  one_mem' := by
    intro x
    simp
  mul_mem' := by
    intro σ τ hσ hτ x
    have hτx :
        ((τ : Gal(L/ℚ)) • x) - x ∈ P ^ 2 := by
      exact hτ x
    have hστx :
        (σ : Gal(L/ℚ)) • (((τ : Gal(L/ℚ)) • x) - x) ∈ P ^ 2 := by
      exact number_inertia_sq (L := L) P σ hτx
    have hσx :
        ((σ : Gal(L/ℚ)) • x) - x ∈ P ^ 2 := by
      exact hσ x
    have hdecomp :
        (((σ * τ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) - x =
          (σ : Gal(L/ℚ)) • (((τ : Gal(L/ℚ)) • x) - x) +
            (((σ : Gal(L/ℚ)) • x) - x) := by
      calc
        (((σ * τ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) - x =
            ((σ : Gal(L/ℚ)) • ((τ : Gal(L/ℚ)) • x)) - x := by
          simp [mul_smul]
        _ =
            (σ : Gal(L/ℚ)) • (((τ : Gal(L/ℚ)) • x) - x) +
              (((σ : Gal(L/ℚ)) • x) - x) := by
          rw [smul_sub]
          abel
    rw [hdecomp]
    exact Ideal.add_mem (P ^ 2) hστx hσx
  inv_mem' := by
    intro σ hσ x
    let τ : P.inertia (Gal(L/ℚ)) := σ⁻¹
    have hσ_on_inv :
        ((σ : Gal(L/ℚ)) • ((τ : Gal(L/ℚ)) • x)) -
            ((τ : Gal(L/ℚ)) • x) ∈ P ^ 2 := by
      exact hσ ((τ : Gal(L/ℚ)) • x)
    have hx_sub :
        x - ((τ : Gal(L/ℚ)) • x) ∈ P ^ 2 := by
      simpa [τ, mul_smul] using hσ_on_inv
    have hneg :
        - (x - ((τ : Gal(L/ℚ)) • x)) ∈ P ^ 2 := by
      exact (P ^ 2).neg_mem hx_sub
    change ((τ : Gal(L/ℚ)) • x) - x ∈ P ^ 2
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg

lemma wild_inertia_subgroup
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) :
    σ ∈ number_wild_subgroup (L := L) P ↔
      ∀ x : NumberField.RingOfIntegers L,
        ((σ : Gal(L/ℚ)) • x) - x ∈ P ^ 2 := by
  rfl

lemma number_wild_mk
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    {σ : P.inertia (Gal(L/ℚ))}
    (hσ : σ ∈ number_wild_subgroup (L := L) P)
    (x : NumberField.RingOfIntegers L) :
    Ideal.Quotient.mk (P ^ 2) (((σ : Gal(L/ℚ)) • x)) =
      Ideal.Quotient.mk (P ^ 2) x := by
  have hcong :
      ((σ : Gal(L/ℚ)) • x) - x ∈ P ^ 2 := by
    exact
      (wild_inertia_subgroup (L := L) P σ).1 hσ x
  exact ideal_sub (P ^ 2) hcong

lemma wild_sq_mk
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    {σ : P.inertia (Gal(L/ℚ))}
    (hσ : ∀ x : NumberField.RingOfIntegers L,
      Ideal.Quotient.mk (P ^ 2) (((σ : Gal(L/ℚ)) • x)) =
        Ideal.Quotient.mk (P ^ 2) x) :
    σ ∈ number_wild_subgroup (L := L) P := by
  rw [wild_inertia_subgroup (L := L) P σ]
  intro x
  exact (ideal_quotient_sub (P ^ 2)).1 (hσ x)

noncomputable def number_inertia_square
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) :
    (NumberField.RingOfIntegers L ⧸ P ^ 2) ≃+*
      (NumberField.RingOfIntegers L ⧸ P ^ 2) := by
  exact
    Ideal.quotientEquiv (P ^ 2) (P ^ 2)
      (MulSemiringAction.toRingEquiv (Gal(L/ℚ))
        (NumberField.RingOfIntegers L) (σ : Gal(L/ℚ)))
      (number_field_sq (L := L) P σ)

lemma number_square_mk
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (x : NumberField.RingOfIntegers L) :
    number_inertia_square (L := L) P σ
        (Ideal.Quotient.mk (P ^ 2) x) =
      Ideal.Quotient.mk (P ^ 2) ((σ : Gal(L/ℚ)) • x) := by
  exact
    Ideal.quotientEquiv_mk
      (I := P ^ 2) (J := P ^ 2)
      (f := MulSemiringAction.toRingEquiv (Gal(L/ℚ))
        (NumberField.RingOfIntegers L) (σ : Gal(L/ℚ)))
      (hIJ := number_field_sq (L := L) P σ) x

noncomputable def number_square_representation
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) :
    P.inertia (Gal(L/ℚ)) →*
      ((NumberField.RingOfIntegers L ⧸ P ^ 2) ≃+*
        (NumberField.RingOfIntegers L ⧸ P ^ 2)) where
  toFun σ :=
    number_inertia_square (L := L) P σ
  map_one' := by
    classical
    ext z
    obtain ⟨x, rfl⟩ :=
      Ideal.Quotient.mk_surjective z
    calc
      number_inertia_square (L := L) P 1
          (Ideal.Quotient.mk (P ^ 2) x) =
        Ideal.Quotient.mk (P ^ 2) (((1 : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) := by
          exact number_square_mk (L := L) P 1 x
      _ = Ideal.Quotient.mk (P ^ 2) x := by
          simp
      _ = (1 :
            (NumberField.RingOfIntegers L ⧸ P ^ 2) ≃+*
              (NumberField.RingOfIntegers L ⧸ P ^ 2))
            (Ideal.Quotient.mk (P ^ 2) x) := by
          rfl
  map_mul' := by
    classical
    intro σ τ
    ext z
    obtain ⟨x, rfl⟩ :=
      Ideal.Quotient.mk_surjective z
    calc
      number_inertia_square (L := L) P (σ * τ)
          (Ideal.Quotient.mk (P ^ 2) x) =
        Ideal.Quotient.mk (P ^ 2)
          ((((σ * τ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x)) := by
          exact
            number_square_mk
              (L := L) P (σ * τ) x
      _ = Ideal.Quotient.mk (P ^ 2)
          ((σ : Gal(L/ℚ)) • ((τ : Gal(L/ℚ)) • x)) := by
          have hmul :
              (((σ * τ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) =
                ((σ : Gal(L/ℚ)) • ((τ : Gal(L/ℚ)) • x)) := by
            simpa using
              (mul_smul (σ : Gal(L/ℚ)) (τ : Gal(L/ℚ)) x)
          exact congrArg (Ideal.Quotient.mk (P ^ 2)) hmul
      _ = number_inertia_square (L := L) P σ
          (Ideal.Quotient.mk (P ^ 2) ((τ : Gal(L/ℚ)) • x)) := by
          exact
            (number_square_mk
              (L := L) P σ ((τ : Gal(L/ℚ)) • x)).symm
      _ = number_inertia_square (L := L) P σ
          (number_inertia_square (L := L) P τ
            (Ideal.Quotient.mk (P ^ 2) x)) := by
          exact
            congrArg
              (number_inertia_square (L := L) P σ)
              (number_square_mk
                (L := L) P τ x).symm
      _ =
          (number_inertia_square (L := L) P σ *
            number_inertia_square (L := L) P τ)
            (Ideal.Quotient.mk (P ^ 2) x) := by
          rfl

lemma square_representation_mk
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (x : NumberField.RingOfIntegers L) :
    number_square_representation (L := L) P σ
        (Ideal.Quotient.mk (P ^ 2) x) =
      Ideal.Quotient.mk (P ^ 2) ((σ : Gal(L/ℚ)) • x) := by
  exact number_square_mk (L := L) P σ x

lemma square_representation_ker
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) :
    (number_square_representation (L := L) P).ker =
      number_wild_subgroup (L := L) P := by
  classical
  ext σ
  constructor
  · intro hσ
    rw [MonoidHom.mem_ker] at hσ
    apply
      wild_sq_mk
        (L := L) P
    intro x
    have hApply :=
      congrArg
        (fun e : (NumberField.RingOfIntegers L ⧸ P ^ 2) ≃+*
            (NumberField.RingOfIntegers L ⧸ P ^ 2) =>
          e (Ideal.Quotient.mk (P ^ 2) x)) hσ
    have hfixed :
        number_square_representation (L := L) P σ
            (Ideal.Quotient.mk (P ^ 2) x) =
          Ideal.Quotient.mk (P ^ 2) x := by
      simpa using hApply
    calc
      Ideal.Quotient.mk (P ^ 2) ((σ : Gal(L/ℚ)) • x) =
          number_square_representation (L := L) P σ
            (Ideal.Quotient.mk (P ^ 2) x) := by
        exact
          (square_representation_mk
            (L := L) P σ x).symm
      _ = Ideal.Quotient.mk (P ^ 2) x := hfixed
  · intro hσ
    rw [MonoidHom.mem_ker]
    ext z
    obtain ⟨x, rfl⟩ :=
      Ideal.Quotient.mk_surjective z
    calc
      number_square_representation (L := L) P σ
          (Ideal.Quotient.mk (P ^ 2) x) =
        Ideal.Quotient.mk (P ^ 2) ((σ : Gal(L/ℚ)) • x) := by
          exact square_representation_mk (L := L) P σ x
      _ = Ideal.Quotient.mk (P ^ 2) x := by
          exact
            number_wild_mk
              (L := L) P hσ x
      _ = (1 :
            (NumberField.RingOfIntegers L ⧸ P ^ 2) ≃+*
              (NumberField.RingOfIntegers L ⧸ P ^ 2))
            (Ideal.Quotient.mk (P ^ 2) x) := by
          rfl

lemma number_square_cotangent
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ)))
    {z : NumberField.RingOfIntegers L ⧸ P ^ 2}
    (hz : z ∈ P.cotangentIdeal) :
    number_inertia_square (L := L) P σ z ∈
      P.cotangentIdeal := by
  classical
  obtain ⟨x, rfl⟩ :=
    Ideal.Quotient.mk_surjective z
  rw [number_square_mk]
  rw [Ideal.mk_mem_cotangentIdeal] at hz ⊢
  exact number_smul_prime (L := L) P σ hz

noncomputable def field_cotangent_ideal
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) :
    P.cotangentIdeal → P.cotangentIdeal :=
  fun z =>
    ⟨number_inertia_square (L := L) P σ z,
      number_square_cotangent
        (L := L) P σ z.property⟩

lemma number_inertia_ideal
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (z : P.cotangentIdeal) :
    ↑(field_cotangent_ideal (L := L) P σ z) =
      number_inertia_square (L := L) P σ
        (z : NumberField.RingOfIntegers L ⧸ P ^ 2) := by
  rfl

lemma number_cotangent_mk
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (x : NumberField.RingOfIntegers L)
    (hx : x ∈ P) :
    field_cotangent_ideal (L := L) P σ
        ⟨Ideal.Quotient.mk (P ^ 2) x, by
          rw [Ideal.mk_mem_cotangentIdeal]
          exact hx⟩ =
      ⟨Ideal.Quotient.mk (P ^ 2) ((σ : Gal(L/ℚ)) • x), by
        rw [Ideal.mk_mem_cotangentIdeal]
        exact number_smul_prime (L := L) P σ hx⟩ := by
  ext
  exact number_square_mk (L := L) P σ x

lemma number_cotangent_zero
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) :
    field_cotangent_ideal (L := L) P σ 0 = 0 := by
  ext
  change
    number_inertia_square (L := L) P σ 0 = 0
  exact map_zero (number_inertia_square (L := L) P σ)

lemma number_cotangent_add
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (z w : P.cotangentIdeal) :
    field_cotangent_ideal (L := L) P σ (z + w) =
      field_cotangent_ideal (L := L) P σ z +
        field_cotangent_ideal (L := L) P σ w := by
  ext
  change
    number_inertia_square (L := L) P σ
        ((z : NumberField.RingOfIntegers L ⧸ P ^ 2) + w) =
      number_inertia_square (L := L) P σ z +
        number_inertia_square (L := L) P σ w
  exact
    map_add
      (number_inertia_square (L := L) P σ)
      (z : NumberField.RingOfIntegers L ⧸ P ^ 2)
      (w : NumberField.RingOfIntegers L ⧸ P ^ 2)

lemma number_cotangent_one
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) (z : P.cotangentIdeal) :
    field_cotangent_ideal (L := L) P 1 z = z := by
  ext
  change
    number_inertia_square (L := L) P 1
        (z : NumberField.RingOfIntegers L ⧸ P ^ 2) =
      (z : NumberField.RingOfIntegers L ⧸ P ^ 2)
  obtain ⟨x, hxz⟩ :=
    Ideal.Quotient.mk_surjective
      (z : NumberField.RingOfIntegers L ⧸ P ^ 2)
  rw [← hxz]
  calc
    number_inertia_square (L := L) P 1
        (Ideal.Quotient.mk (P ^ 2) x) =
      Ideal.Quotient.mk (P ^ 2)
        (((1 : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) := by
        exact number_square_mk (L := L) P 1 x
    _ = Ideal.Quotient.mk (P ^ 2) x := by
        simp

lemma number_cotangent_mul
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ τ : P.inertia (Gal(L/ℚ))) (z : P.cotangentIdeal) :
    field_cotangent_ideal (L := L) P (σ * τ) z =
      field_cotangent_ideal (L := L) P σ
        (field_cotangent_ideal (L := L) P τ z) := by
  ext
  change
    number_inertia_square (L := L) P (σ * τ)
        (z : NumberField.RingOfIntegers L ⧸ P ^ 2) =
      number_inertia_square (L := L) P σ
        (number_inertia_square (L := L) P τ
          (z : NumberField.RingOfIntegers L ⧸ P ^ 2))
  obtain ⟨x, hxz⟩ :=
    Ideal.Quotient.mk_surjective
      (z : NumberField.RingOfIntegers L ⧸ P ^ 2)
  rw [← hxz]
  calc
    number_inertia_square (L := L) P (σ * τ)
        (Ideal.Quotient.mk (P ^ 2) x) =
      Ideal.Quotient.mk (P ^ 2)
        ((((σ * τ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x)) := by
        exact
          number_square_mk
            (L := L) P (σ * τ) x
    _ = Ideal.Quotient.mk (P ^ 2)
        ((σ : Gal(L/ℚ)) • ((τ : Gal(L/ℚ)) • x)) := by
        have hmul :
            (((σ * τ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) =
              ((σ : Gal(L/ℚ)) • ((τ : Gal(L/ℚ)) • x)) := by
          simpa using
            (mul_smul (σ : Gal(L/ℚ)) (τ : Gal(L/ℚ)) x)
        exact congrArg (Ideal.Quotient.mk (P ^ 2)) hmul
    _ = number_inertia_square (L := L) P σ
        (Ideal.Quotient.mk (P ^ 2) ((τ : Gal(L/ℚ)) • x)) := by
        exact
          (number_square_mk
            (L := L) P σ ((τ : Gal(L/ℚ)) • x)).symm
    _ = number_inertia_square (L := L) P σ
        (number_inertia_square (L := L) P τ
          (Ideal.Quotient.mk (P ^ 2) x)) := by
        exact
          congrArg
            (number_inertia_square (L := L) P σ)
            (number_square_mk
              (L := L) P τ x).symm

lemma number_cotangent_inv
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (z : P.cotangentIdeal) :
    field_cotangent_ideal (L := L) P σ⁻¹
        (field_cotangent_ideal (L := L) P σ z) = z := by
  calc
    field_cotangent_ideal (L := L) P σ⁻¹
        (field_cotangent_ideal (L := L) P σ z) =
      field_cotangent_ideal (L := L) P (σ⁻¹ * σ) z := by
        exact
          (number_cotangent_mul
            (L := L) P σ⁻¹ σ z).symm
    _ = field_cotangent_ideal (L := L) P 1 z := by
        rw [inv_mul_cancel]
    _ = z := by
        exact number_cotangent_one (L := L) P z

lemma inertia_cotangent_inv
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (z : P.cotangentIdeal) :
    field_cotangent_ideal (L := L) P σ
        (field_cotangent_ideal (L := L) P σ⁻¹ z) = z := by
  calc
    field_cotangent_ideal (L := L) P σ
        (field_cotangent_ideal (L := L) P σ⁻¹ z) =
      field_cotangent_ideal (L := L) P (σ * σ⁻¹) z := by
        exact
          (number_cotangent_mul
            (L := L) P σ σ⁻¹ z).symm
    _ = field_cotangent_ideal (L := L) P 1 z := by
        rw [mul_inv_cancel]
    _ = z := by
        exact number_cotangent_one (L := L) P z

noncomputable def inertia_cotangent_equiv
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) :
    P.cotangentIdeal ≃ P.cotangentIdeal where
  toFun := field_cotangent_ideal (L := L) P σ
  invFun := field_cotangent_ideal (L := L) P σ⁻¹
  left_inv := by
    intro z
    exact number_cotangent_inv (L := L) P σ z
  right_inv := by
    intro z
    exact inertia_cotangent_inv (L := L) P σ z

lemma inertia_cotangent_ideal
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (z : P.cotangentIdeal) :
    inertia_cotangent_equiv (L := L) P σ z =
      field_cotangent_ideal (L := L) P σ z := by
  rfl

noncomputable def number_cotangent_equiv
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) :
    AddAut P.cotangentIdeal where
  toFun := field_cotangent_ideal (L := L) P σ
  invFun := field_cotangent_ideal (L := L) P σ⁻¹
  left_inv := by
    intro z
    exact number_cotangent_inv (L := L) P σ z
  right_inv := by
    intro z
    exact inertia_cotangent_inv (L := L) P σ z
  map_add' := by
    intro z w
    exact number_cotangent_add (L := L) P σ z w

lemma number_cotangent_ideal
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (z : P.cotangentIdeal) :
    number_cotangent_equiv (L := L) P σ z =
      field_cotangent_ideal (L := L) P σ z := by
  rfl

noncomputable def cotangent_add_representation
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) :
    P.inertia (Gal(L/ℚ)) →* AddAut P.cotangentIdeal where
  toFun σ := number_cotangent_equiv (L := L) P σ
  map_one' := by
    apply AddEquiv.ext
    intro z
    exact number_cotangent_one (L := L) P z
  map_mul' := by
    intro σ τ
    apply AddEquiv.ext
    intro z
    exact number_cotangent_mul (L := L) P σ τ z

lemma number_inertia_representation
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (z : P.cotangentIdeal) :
    cotangent_add_representation (L := L) P σ z =
      field_cotangent_ideal (L := L) P σ z := by
  rfl

lemma cotangent_representation_ker
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) :
    σ ∈ (cotangent_add_representation (L := L) P).ker ↔
      ∀ z : P.cotangentIdeal,
        field_cotangent_ideal (L := L) P σ z = z := by
  constructor
  · intro hσ z
    rw [MonoidHom.mem_ker] at hσ
    have hApply :=
      congrArg
        (fun e : AddAut P.cotangentIdeal => e z) hσ
    simpa [number_inertia_representation]
      using hApply
  · intro hσ
    rw [MonoidHom.mem_ker]
    apply AddEquiv.ext
    intro z
    exact hσ z

lemma number_cotangent_representation
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) :
    (cotangent_add_representation (L := L) P).ker =
      {σ : P.inertia (Gal(L/ℚ)) |
        ∀ z : P.cotangentIdeal,
          field_cotangent_ideal (L := L) P σ z = z} := by
  ext σ
  exact cotangent_representation_ker
    (L := L) P σ

lemma wild_cotangent_fixed
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    {σ : P.inertia (Gal(L/ℚ))}
    (hσ : σ ∈ number_wild_subgroup (L := L) P)
    (z : P.cotangentIdeal) :
    field_cotangent_ideal (L := L) P σ z = z := by
  ext
  change
    number_inertia_square (L := L) P σ
        (z : NumberField.RingOfIntegers L ⧸ P ^ 2) =
      (z : NumberField.RingOfIntegers L ⧸ P ^ 2)
  obtain ⟨x, hxz⟩ :=
    Ideal.Quotient.mk_surjective
      (z : NumberField.RingOfIntegers L ⧸ P ^ 2)
  rw [← hxz]
  exact number_wild_mk (L := L) P hσ x

lemma wild_cotangent_representation
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) :
    number_wild_subgroup (L := L) P ≤
      (cotangent_add_representation (L := L) P).ker := by
  intro σ hσ
  rw [cotangent_representation_ker
    (L := L) P σ]
  intro z
  exact wild_cotangent_fixed (L := L) P hσ z

lemma number_cotangent_sq
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) :
    (∀ z : P.cotangentIdeal,
        field_cotangent_ideal (L := L) P σ z = z) ↔
      ∀ x : P,
        ((σ : Gal(L/ℚ)) • (x : NumberField.RingOfIntegers L)) -
          (x : NumberField.RingOfIntegers L) ∈ P ^ 2 := by
  constructor
  · intro hfixed x
    let z : P.cotangentIdeal :=
      ⟨Ideal.Quotient.mk (P ^ 2) (x : NumberField.RingOfIntegers L), by
        rw [Ideal.mk_mem_cotangentIdeal]
        exact x.property⟩
    have hzfixed :
        field_cotangent_ideal (L := L) P σ z = z := by
      exact hfixed z
    have hquot :
        Ideal.Quotient.mk (P ^ 2)
            ((σ : Gal(L/ℚ)) • (x : NumberField.RingOfIntegers L)) =
          Ideal.Quotient.mk (P ^ 2) (x : NumberField.RingOfIntegers L) := by
      have hzval :=
        congrArg
          (fun y : P.cotangentIdeal =>
            (y : NumberField.RingOfIntegers L ⧸ P ^ 2)) hzfixed
      change
        number_inertia_square (L := L) P σ
            (z : NumberField.RingOfIntegers L ⧸ P ^ 2) =
          (z : NumberField.RingOfIntegers L ⧸ P ^ 2) at hzval
      change
        number_inertia_square (L := L) P σ
            (Ideal.Quotient.mk (P ^ 2) (x : NumberField.RingOfIntegers L)) =
          Ideal.Quotient.mk (P ^ 2) (x : NumberField.RingOfIntegers L) at hzval
      rw [number_square_mk] at hzval
      exact hzval
    exact (ideal_quotient_sub (P ^ 2)).1 hquot
  · intro hP z
    ext
    change
      number_inertia_square (L := L) P σ
          (z : NumberField.RingOfIntegers L ⧸ P ^ 2) =
        (z : NumberField.RingOfIntegers L ⧸ P ^ 2)
    obtain ⟨x, hxz⟩ :=
      Ideal.Quotient.mk_surjective
        (z : NumberField.RingOfIntegers L ⧸ P ^ 2)
    have hxP : x ∈ P := by
      have hzmem : (z : NumberField.RingOfIntegers L ⧸ P ^ 2) ∈ P.cotangentIdeal :=
        z.property
      rw [← hxz] at hzmem
      rwa [Ideal.mk_mem_cotangentIdeal] at hzmem
    have hquot :
        Ideal.Quotient.mk (P ^ 2) (((σ : Gal(L/ℚ)) • x)) =
          Ideal.Quotient.mk (P ^ 2) x := by
      exact ideal_sub (P ^ 2) (hP ⟨x, hxP⟩)
    rw [← hxz]
    calc
      number_inertia_square (L := L) P σ
          (Ideal.Quotient.mk (P ^ 2) x) =
        Ideal.Quotient.mk (P ^ 2) (((σ : Gal(L/ℚ)) • x)) := by
          exact number_square_mk (L := L) P σ x
      _ = Ideal.Quotient.mk (P ^ 2) x := hquot

lemma number_cast_prime
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    (Nat.card P.ResidueField : NumberField.RingOfIntegers L) ∈ P := by
  classical
  haveI : Finite P.ResidueField :=
    number_local_residue (L := L) hq P
  letI : Fintype P.ResidueField :=
    Fintype.ofFinite P.ResidueField
  rw [← Ideal.algebraMap_residueField_eq_zero (I := P)]
  simp [Nat.card_eq_fintype_card]

lemma number_sub_prime
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (x : NumberField.RingOfIntegers L) :
    x ^ Nat.card P.ResidueField - x ∈ P := by
  classical
  haveI : Finite P.ResidueField :=
    number_local_residue (L := L) hq P
  letI : Fintype P.ResidueField :=
    Fintype.ofFinite P.ResidueField
  have hpow :
      (algebraMap (NumberField.RingOfIntegers L) P.ResidueField x) ^
          Nat.card P.ResidueField =
        algebraMap (NumberField.RingOfIntegers L) P.ResidueField x := by
    simpa [Nat.card_eq_fintype_card] using
      (FiniteField.pow_card
        (algebraMap (NumberField.RingOfIntegers L) P.ResidueField x))
  exact
    (ideal_residue_sub
      (I := P) (x := x ^ Nat.card P.ResidueField) (y := x)).1
      (by simpa using hpow)

lemma sq_cast_mul
    {R : Type*} [CommRing R] {n : ℕ} {x d : R}
    (hd2 : d ^ 2 = 0) :
    (x + d) ^ n = x ^ n + (n : R) * x ^ (n - 1) * d := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ', ih]
      cases n with
      | zero =>
          simp
      | succ n =>
          simp [pow_succ, Nat.cast_add, Nat.cast_one]
          ring_nf
          rw [hd2]
          simp

lemma sub_sq_cast
    {R : Type*} [CommRing R] (I : Ideal R) {n : ℕ} {x d : R}
    (hd : d ∈ I) (hn : (n : R) ∈ I) :
    (x + d) ^ n - x ^ n ∈ I ^ 2 := by
  classical
  let Q : Type _ := R ⧸ I ^ 2
  let mk : R →+* Q := Ideal.Quotient.mk (I ^ 2)
  have hd2mem :
      d ^ 2 ∈ I ^ 2 := by
    simpa [pow_two] using Ideal.mul_mem_mul hd hd
  have hndmem :
      (n : R) * d ∈ I ^ 2 := by
    simpa [pow_two] using Ideal.mul_mem_mul hn hd
  have hd2quot :
      (mk d : Q) ^ 2 = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hd2mem
  have hndquot :
      (n : Q) * mk d = 0 := by
    have hmk :
        mk ((n : R) * d) = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hndmem
    simpa [mk] using hmk
  have hpoweq :
      (mk (x + d) : Q) ^ n = (mk x : Q) ^ n := by
    have haux :
        ((mk x : Q) + mk d) ^ n =
          (mk x : Q) ^ n + (n : Q) * (mk x : Q) ^ (n - 1) * mk d := by
      exact
        sq_cast_mul
          (R := Q) (n := n) (x := mk x) (d := mk d) hd2quot
    have hterm :
        (n : Q) * (mk x : Q) ^ (n - 1) * mk d = 0 := by
      calc
        (n : Q) * (mk x : Q) ^ (n - 1) * mk d =
            (mk x : Q) ^ (n - 1) * ((n : Q) * mk d) := by
              ring
        _ = 0 := by
          rw [hndquot, mul_zero]
    rw [map_add]
    rw [haux, hterm, add_zero]
  have hzero :
      mk ((x + d) ^ n - x ^ n) = 0 := by
    rw [map_sub, map_pow, map_pow, hpoweq, sub_self]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hzero

lemma sub_sq_self
    {R : Type*} [CommRing R] (I : Ideal R) {n : ℕ} {x y : R}
    (hpowdiff : y ^ n - y - (x ^ n - x) ∈ I ^ 2)
    (hpows : y ^ n - x ^ n ∈ I ^ 2) :
    y - x ∈ I ^ 2 := by
  have hsub :
      (y ^ n - y - (x ^ n - x)) - (y ^ n - x ^ n) ∈ I ^ 2 := by
    exact (I ^ 2).sub_mem hpowdiff hpows
  have hneg :
      -(y - x) ∈ I ^ 2 := by
    convert hsub using 1
    ring
  simpa using (I ^ 2).neg_mem hneg

lemma number_smul_sq
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : P.inertia (Gal(L/ℚ)))
    (hP : ∀ x : P,
      ((σ : Gal(L/ℚ)) • (x : NumberField.RingOfIntegers L)) -
        (x : NumberField.RingOfIntegers L) ∈ P ^ 2) :
    ∀ x : NumberField.RingOfIntegers L,
      ((σ : Gal(L/ℚ)) • x) - x ∈ P ^ 2 := by
  classical
  intro x
  let N : ℕ := Nat.card P.ResidueField
  have hdelta :
      ((σ : Gal(L/ℚ)) • x) - x ∈ P := by
    exact number_smul_sub (L := L) P σ x
  have hcardP :
      (N : NumberField.RingOfIntegers L) ∈ P := by
    simpa [N] using
      number_cast_prime (L := L) hq P
  have hpowP :
      x ^ N - x ∈ P := by
    simpa [N] using
      number_sub_prime (L := L) hq P x
  have hPpow :
      ((σ : Gal(L/ℚ)) • (x ^ N - x)) - (x ^ N - x) ∈ P ^ 2 := by
    exact hP ⟨x ^ N - x, hpowP⟩
  have hpowdiff :
      (((σ : Gal(L/ℚ)) • x) ^ N - ((σ : Gal(L/ℚ)) • x)) -
          (x ^ N - x) ∈ P ^ 2 := by
    simpa [smul_sub, smul_pow'] using hPpow
  have hpows :
      ((σ : Gal(L/ℚ)) • x) ^ N - x ^ N ∈ P ^ 2 := by
    have hbinom :
        (x + (((σ : Gal(L/ℚ)) • x) - x)) ^ N - x ^ N ∈ P ^ 2 := by
      exact
        sub_sq_cast
          (I := P) (n := N) (x := x)
          (d := ((σ : Gal(L/ℚ)) • x) - x) hdelta hcardP
    convert hbinom using 1
    ring
  exact
    sub_sq_self
      (I := P) (n := N) (x := x) (y := ((σ : Gal(L/ℚ)) • x))
      hpowdiff hpows

lemma number_cotangent_wild
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    (cotangent_add_representation (L := L) P).ker ≤
      number_wild_subgroup (L := L) P := by
  intro σ hσ
  rw [wild_inertia_subgroup (L := L) P σ]
  have hfixed :
      ∀ z : P.cotangentIdeal,
        field_cotangent_ideal (L := L) P σ z = z := by
    exact
      (cotangent_representation_ker
        (L := L) P σ).1 hσ
  have hP :
      ∀ x : P,
        ((σ : Gal(L/ℚ)) • (x : NumberField.RingOfIntegers L)) -
          (x : NumberField.RingOfIntegers L) ∈ P ^ 2 := by
    exact
      (number_cotangent_sq
        (L := L) P σ).1 hfixed
  exact
    number_smul_sq
      (L := L) hq P σ hP

lemma cotangent_representation_wild
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    (cotangent_add_representation (L := L) P).ker =
      number_wild_subgroup (L := L) P := by
  apply le_antisymm
  · exact
      number_cotangent_wild
        (L := L) hq P
  · exact
      wild_cotangent_representation
        (L := L) P

lemma representation_cotangent_fixed
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    {σ : P.inertia (Gal(L/ℚ))}
    (hσ : σ ∈ (number_square_representation (L := L) P).ker)
    (z : P.cotangentIdeal) :
    field_cotangent_ideal (L := L) P σ z = z := by
  have hWild :
      σ ∈ number_wild_subgroup (L := L) P := by
    simpa [square_representation_ker (L := L) P] using hσ
  exact
    wild_cotangent_fixed
      (L := L) P hWild z

noncomputable def dimensionalRepresentationScalar
    {K : Type*} {G0 : Type*} {V : Type*} [Field K] [Group G0] [AddCommGroup V] [Module K V]
    (ρ : G0 →* V ≃ₗ[K] V) (v : V)
    (hv_span : ∀ w : V, ∃ a : K, a • v = w) (g : G0) : K :=
  Classical.choose (hv_span (ρ g v))

lemma dimensional_representation_smul
    {K : Type*} {G0 : Type*} {V : Type*} [Field K] [Group G0] [AddCommGroup V] [Module K V]
    (ρ : G0 →* V ≃ₗ[K] V) (v : V)
    (hv_span : ∀ w : V, ∃ a : K, a • v = w) (g : G0) :
    dimensionalRepresentationScalar ρ v hv_span g • v = ρ g v := by
  exact Classical.choose_spec (hv_span (ρ g v))

lemma dimensional_representation_scalar
    {K : Type*} {G0 : Type*} {V : Type*} [Field K] [Group G0] [AddCommGroup V] [Module K V]
    (ρ : G0 →* V ≃ₗ[K] V) (v : V) (hv_ne_zero : v ≠ 0)
    (hv_span : ∀ w : V, ∃ a : K, a • v = w) (g : G0) :
    dimensionalRepresentationScalar ρ v hv_span g ≠ 0 := by
  intro hzero
  have hmap_zero : ρ g v = 0 := by
    calc
      ρ g v =
          dimensionalRepresentationScalar ρ v hv_span g • v := by
            exact (dimensional_representation_smul ρ v hv_span g).symm
      _ = 0 := by
            rw [hzero, zero_smul]
  have hv_zero : v = 0 := by
    exact (ρ g).injective (by simpa using hmap_zero)
  exact hv_ne_zero hv_zero

noncomputable def dimensionalLinearCharacter
    {K : Type*} {G0 : Type*} {V : Type*} [Field K] [Group G0] [AddCommGroup V] [Module K V]
    (ρ : G0 →* V ≃ₗ[K] V) (v : V) (hv_ne_zero : v ≠ 0)
    (hv_span : ∀ w : V, ∃ a : K, a • v = w) : G0 →* Kˣ where
  toFun g :=
    Units.mk0
      (dimensionalRepresentationScalar ρ v hv_span g)
      (dimensional_representation_scalar ρ v hv_ne_zero hv_span g)
  map_one' := by
    apply Units.ext
    change dimensionalRepresentationScalar ρ v hv_span 1 = 1
    apply smul_left_injective K hv_ne_zero
    calc
      dimensionalRepresentationScalar ρ v hv_span 1 • v =
          ρ 1 v := by
            exact dimensional_representation_smul ρ v hv_span 1
      _ = v := by
            simp
      _ = (1 : K) • v := by
            simp
  map_mul' := by
    intro g h
    apply Units.ext
    change
      dimensionalRepresentationScalar ρ v hv_span (g * h) =
        dimensionalRepresentationScalar ρ v hv_span g *
          dimensionalRepresentationScalar ρ v hv_span h
    apply smul_left_injective K hv_ne_zero
    calc
      dimensionalRepresentationScalar ρ v hv_span (g * h) • v =
          ρ (g * h) v := by
            exact dimensional_representation_smul ρ v hv_span (g * h)
      _ = ρ g (ρ h v) := by
            rw [map_mul]
            rfl
      _ = ρ g (dimensionalRepresentationScalar ρ v hv_span h • v) := by
            rw [dimensional_representation_smul]
      _ = dimensionalRepresentationScalar ρ v hv_span h • ρ g v := by
            exact map_smul (ρ g)
              (dimensionalRepresentationScalar ρ v hv_span h) v
      _ =
          dimensionalRepresentationScalar ρ v hv_span h •
            (dimensionalRepresentationScalar ρ v hv_span g • v) := by
            rw [dimensional_representation_smul]
      _ =
          (dimensionalRepresentationScalar ρ v hv_span h *
            dimensionalRepresentationScalar ρ v hv_span g) • v := by
            rw [mul_smul]
      _ =
          (dimensionalRepresentationScalar ρ v hv_span g *
            dimensionalRepresentationScalar ρ v hv_span h) • v := by
            rw [mul_comm]

lemma dimensional_character_smul
    {K : Type*} {G0 : Type*} {V : Type*} [Field K] [Group G0] [AddCommGroup V] [Module K V]
    (ρ : G0 →* V ≃ₗ[K] V) (v : V) (hv_ne_zero : v ≠ 0)
    (hv_span : ∀ w : V, ∃ a : K, a • v = w) (g : G0) :
    ((dimensionalLinearCharacter ρ v hv_ne_zero hv_span g : K) • v) = ρ g v := by
  exact dimensional_representation_smul ρ v hv_span g

lemma dimensional_character_ker
    {K : Type*} {G0 : Type*} {V : Type*} [Field K] [Group G0] [AddCommGroup V] [Module K V]
    (ρ : G0 →* V ≃ₗ[K] V) (v : V) (hv_ne_zero : v ≠ 0)
    (hv_span : ∀ w : V, ∃ a : K, a • v = w) :
    (dimensionalLinearCharacter ρ v hv_ne_zero hv_span).ker = ρ.ker := by
  ext g
  constructor
  · intro hg
    rw [MonoidHom.mem_ker] at hg ⊢
    apply LinearEquiv.ext
    intro w
    obtain ⟨a, ha⟩ := hv_span w
    have hscalar :
        (dimensionalLinearCharacter ρ v hv_ne_zero hv_span g : K) = 1 := by
      exact congrArg Units.val hg
    calc
      ρ g w = ρ g (a • v) := by
          rw [ha]
      _ = a • ρ g v := by
          exact map_smul (ρ g) a v
      _ = a • ((dimensionalLinearCharacter ρ v hv_ne_zero hv_span g : K) • v) := by
          rw [dimensional_character_smul]
      _ = a • ((1 : K) • v) := by
          rw [hscalar]
      _ = a • v := by
          rw [one_smul]
      _ = w := ha
  · intro hg
    rw [MonoidHom.mem_ker] at hg ⊢
    apply Units.ext
    change
      dimensionalRepresentationScalar ρ v hv_span g = 1
    apply smul_left_injective K hv_ne_zero
    calc
      dimensionalRepresentationScalar ρ v hv_span g • v =
          ρ g v := by
            exact dimensional_representation_smul ρ v hv_span g
      _ = (1 : V ≃ₗ[K] V) v := by
            rw [hg]
      _ = (1 : K) • v := by
            simp

lemma dimensional_linear_character
    {K : Type*} {G0 : Type*} {V : Type*} [Field K] [Group G0] [AddCommGroup V] [Module K V]
    (ρ : G0 →* V ≃ₗ[K] V) (v : V) (hv_ne_zero : v ≠ 0)
    (hv_span : ∀ w : V, ∃ a : K, a • v = w) :
    ∃ χ : G0 →* Kˣ, χ.ker = ρ.ker := by
  refine ⟨dimensionalLinearCharacter ρ v hv_ne_zero hv_span, ?_⟩
  exact dimensional_character_ker ρ v hv_ne_zero hv_span

def dimensionalSpansElement
    {K : Type*} {V : Type*} [Field K] [AddCommGroup V]
    (moduleInst : Module K V) (v : V) : Prop :=
  letI : Module K V := moduleInst
  ∀ w : V, ∃ a : K, a • v = w

def additiveRepresentationModule
    {K : Type*} {G0 : Type*} {V : Type*} [Field K] [Group G0] [AddCommGroup V]
    (moduleInst : Module K V) (ρadd : G0 →* AddAut V) : Prop :=
  letI : Module K V := moduleInst
  ∀ g : G0, ∀ a : K, ∀ v : V, ρadd g (a • v) = a • ρadd g v

lemma dimensional_spans_element
    {K : Type*} {G0 : Type*} {V : Type*} [Field K] [Group G0] [AddCommGroup V] [Module K V]
    (ρ : G0 →* V ≃ₗ[K] V) (v : V) (hv_ne_zero : v ≠ 0)
    (hv_span : dimensionalSpansElement
      (K := K) (V := V) (inferInstance : Module K V) v) :
    ∃ χ : G0 →* Kˣ, χ.ker = ρ.ker := by
  have hv_span' : ∀ w : V, ∃ a : K, a • v = w := by
    dsimp [dimensionalSpansElement] at hv_span
    exact hv_span
  exact dimensional_linear_character ρ v hv_ne_zero hv_span'

lemma additive_representation_linear
    {K : Type*} {G0 : Type*} {V : Type*} [Field K] [Group G0] [AddCommGroup V] [Module K V]
    (ρadd : G0 →* AddAut V)
    (hsmul : additiveRepresentationModule
      (K := K) (G0 := G0) (V := V) (inferInstance : Module K V) ρadd) :
    ∃ ρlin : G0 →* V ≃ₗ[K] V, ρlin.ker = ρadd.ker := by
  have hsmul_linear : ∀ g : G0, ∀ a : K, ∀ v : V, ρadd g (a • v) = a • ρadd g v := by
    dsimp [additiveRepresentationModule] at hsmul
    exact hsmul
  let ρlin : G0 →* V ≃ₗ[K] V := {
    toFun := fun g => AddEquiv.toLinearEquiv (R := K) (ρadd g) (hsmul_linear g)
    map_one' := by
      apply LinearEquiv.ext
      intro v
      change ρadd 1 v = v
      simp
    map_mul' := by
      intro g h
      apply LinearEquiv.ext
      intro v
      change ρadd (g * h) v = (ρadd g * ρadd h) v
      exact congrArg (fun e : AddAut V => e v) (ρadd.map_mul g h)
  }
  refine ⟨ρlin, ?_⟩
  ext g
  constructor
  · intro hg
    rw [MonoidHom.mem_ker] at hg ⊢
    apply AddEquiv.ext
    intro v
    have hApply :=
      congrArg (fun e : V ≃ₗ[K] V => e v) hg
    simpa [ρlin] using hApply
  · intro hg
    rw [MonoidHom.mem_ker] at hg ⊢
    apply LinearEquiv.ext
    intro v
    have hApply :=
      congrArg (fun e : AddAut V => e v) hg
    simpa [ρlin] using hApply








@[reducible]
noncomputable def cotangent_residue_module
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    Module P.ResidueField P.Cotangent := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  exact
    Module.compHom P.Cotangent
      ((idealResidueMaximal P).symm.toRingHom)







@[reducible]
noncomputable def number_residue_module
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    Module P.ResidueField P.cotangentIdeal := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  exact P.cotangentEquivIdeal.symm.toAddEquiv.module P.ResidueField

noncomputable def number_cotangent_residue
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    letI : Module P.ResidueField P.cotangentIdeal :=
      number_residue_module (L := L) hq P
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    P.cotangentIdeal ≃ₗ[P.ResidueField] P.Cotangent := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  letI : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  exact P.cotangentEquivIdeal.symm.toAddEquiv.linearEquiv P.ResidueField

lemma number_cotangent_module
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∃ _moduleInst : Module P.ResidueField P.cotangentIdeal, True := by
  exact
    ⟨number_residue_module (L := L) _hq P, trivial⟩

lemma number_residue_surjective
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    Function.Surjective
      (algebraMap (NumberField.RingOfIntegers L) P.ResidueField) := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  intro a
  obtain ⟨abar, habar⟩ :=
    (idealResidueMaximal P).surjective a
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective abar
  refine ⟨r, ?_⟩
  rw [← habar, ← hr]
  change algebraMap (NumberField.RingOfIntegers L) P.ResidueField r =
    algebraMap (NumberField.RingOfIntegers L ⧸ P) P.ResidueField
      (Ideal.Quotient.mk P r)
  simp

noncomputable def field_inertia_cotangent
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : P.inertia (Gal(L/ℚ))) :
    letI : Module P.ResidueField P.cotangentIdeal :=
      number_residue_module (L := L) hq P
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    P.Cotangent → P.Cotangent := by
  classical
  letI : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  let e :=
    number_cotangent_residue (L := L) hq P
  exact fun y =>
    e (cotangent_add_representation (L := L) P σ (e.symm y))

lemma number_inertia_cotangent
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : P.inertia (Gal(L/ℚ))) (z : P.cotangentIdeal) :
    letI : Module P.ResidueField P.cotangentIdeal :=
      number_residue_module (L := L) hq P
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    field_inertia_cotangent (L := L) hq P σ
        (number_cotangent_residue (L := L) hq P z) =
      number_cotangent_residue (L := L) hq P
        (cotangent_add_representation (L := L) P σ z) := by
  classical
  letI : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  simp [field_inertia_cotangent]

lemma residue_smul_cotangent
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (r : NumberField.RingOfIntegers L) (x : P) :
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    (algebraMap (NumberField.RingOfIntegers L) P.ResidueField r) • P.toCotangent x =
      P.toCotangent (r • x) := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  have hscalar :
      (idealResidueMaximal P).symm
          (algebraMap (NumberField.RingOfIntegers L) P.ResidueField r) =
        algebraMap (NumberField.RingOfIntegers L)
          (NumberField.RingOfIntegers L ⧸ P) r := by
    rw [RingEquiv.symm_apply_eq]
    change algebraMap (NumberField.RingOfIntegers L) P.ResidueField r =
      algebraMap (NumberField.RingOfIntegers L ⧸ P) P.ResidueField
        (Ideal.Quotient.mk P r)
    simp
  change
    (idealResidueMaximal P).symm
        (algebraMap (NumberField.RingOfIntegers L) P.ResidueField r) •
        P.toCotangent x =
      P.toCotangent (r • x)
  rw [hscalar]
  rfl

lemma number_smul_cotangent
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (r : NumberField.RingOfIntegers L) (y : P.Cotangent) :
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    (algebraMap (NumberField.RingOfIntegers L) P.ResidueField r) • y =
      r • y := by
  classical
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  obtain ⟨x, rfl⟩ := P.toCotangent_surjective y
  rw [residue_smul_cotangent (L := L) hq P r x]
  rfl

lemma number_compl_ne
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (s : P.primeCompl) :
    algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (s : NumberField.RingOfIntegers L) ≠ 0 := by
  classical
  change
    ¬ algebraMap (NumberField.RingOfIntegers L) P.ResidueField
        (s : NumberField.RingOfIntegers L) = 0
  rw [Ideal.algebraMap_residueField_eq_zero]
  exact s.property

lemma cotangent_compl_bijective
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (s : P.primeCompl) :
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    Function.Bijective
      (fun y : P.Cotangent => (s : NumberField.RingOfIntegers L) • y) := by
  classical
  let R := NumberField.RingOfIntegers L
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  let a : P.ResidueField := algebraMap R P.ResidueField (s : R)
  have ha : a ≠ 0 := by
    exact number_compl_ne (L := L) hq P s
  have hscalar :
      ∀ y : P.Cotangent, (s : R) • y = a • y := by
    intro y
    exact
      (number_smul_cotangent
        (L := L) hq P (s : R) y).symm
  constructor
  · intro x y hxy
    have hxy_residue : a • x = a • y := by
      simpa [hscalar x, hscalar y] using hxy
    calc
      x = (a⁻¹ * a) • x := by
        rw [inv_mul_cancel₀ ha, one_smul]
      _ = a⁻¹ • (a • x) := by
        rw [smul_smul]
      _ = a⁻¹ • (a • y) := by
        rw [hxy_residue]
      _ = (a⁻¹ * a) • y := by
        rw [smul_smul]
      _ = y := by
        rw [inv_mul_cancel₀ ha, one_smul]
  · intro y
    refine ⟨a⁻¹ • y, ?_⟩
    calc
      (s : R) • (a⁻¹ • y) = a • (a⁻¹ • y) := by
        rw [hscalar]
      _ = (a * a⁻¹) • y := by
        rw [smul_smul]
      _ = y := by
        rw [mul_inv_cancel₀ ha, one_smul]

noncomputable def cotangent_compl_aut
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (s : P.primeCompl) :
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    P.Cotangent ≃ₗ[P.ResidueField] P.Cotangent := by
  classical
  let R := NumberField.RingOfIntegers L
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  let a : P.ResidueField := algebraMap R P.ResidueField (s : R)
  have hscalar :
      ∀ y : P.Cotangent, (s : R) • y = a • y := by
    intro y
    exact
      (number_smul_cotangent
        (L := L) hq P (s : R) y).symm
  have hbij_a : Function.Bijective (fun y : P.Cotangent => a • y) := by
    have hbij_s :=
      cotangent_compl_bijective (L := L) hq P s
    constructor
    · intro x y hxy
      exact hbij_s.1 (by simpa [hscalar x, hscalar y] using hxy)
    · intro y
      obtain ⟨x, hx⟩ := hbij_s.2 y
      exact ⟨x, by simpa [hscalar x] using hx⟩
  let f : P.Cotangent →ₗ[P.ResidueField] P.Cotangent := {
    toFun := fun y => a • y
    map_add' := by
      intro x y
      simp [smul_add]
    map_smul' := by
      intro b y
      simp [smul_smul, mul_comm]
  }
  exact LinearEquiv.ofBijective f hbij_a

lemma cotangent_localized_id
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    let R := NumberField.RingOfIntegers L
    IsLocalizedModule P.primeCompl (LinearMap.id : P.Cotangent →ₗ[R] P.Cotangent) := by
  classical
  let R := NumberField.RingOfIntegers L
  refine
    { map_units := ?_
      surj := ?_
      exists_of_eq := ?_ }
  · intro s
    rw [Module.End.isUnit_iff]
    simpa [Module.algebraMap_end_apply] using
      (cotangent_compl_bijective (L := L) hq P s)
  · intro y
    exact ⟨⟨y, 1⟩, by simp⟩
  · intro x₁ x₂ h
    exact ⟨1, by simpa using h⟩

noncomputable def number_localized_module
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    let R := NumberField.RingOfIntegers L
    P.Cotangent ≃ₗ[R] LocalizedModule P.primeCompl P.Cotangent := by
  classical
  let R := NumberField.RingOfIntegers L
  haveI :
      IsLocalizedModule P.primeCompl
        (LinearMap.id : P.Cotangent →ₗ[R] P.Cotangent) :=
    cotangent_localized_id (L := L) hq P
  exact
    (IsLocalizedModule.iso P.primeCompl
      (LinearMap.id : P.Cotangent →ₗ[R] P.Cotangent)).symm

lemma cotangent_localized_module
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (y : P.Cotangent) :
    number_localized_module (L := L) hq P y =
      LocalizedModule.mk y (1 : P.primeCompl) := by
  classical
  let R := NumberField.RingOfIntegers L
  haveI :
      IsLocalizedModule P.primeCompl
        (LinearMap.id : P.Cotangent →ₗ[R] P.Cotangent) :=
    cotangent_localized_id (L := L) hq P
  simpa [number_localized_module] using
    (IsLocalizedModule.iso_symm_apply
      (S := P.primeCompl)
      (f := (LinearMap.id : P.Cotangent →ₗ[R] P.Cotangent))
      y)

noncomputable def cotangent_tensor_localization
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    let R := NumberField.RingOfIntegers L
    let Rₚ := Localization.AtPrime P
    P.Cotangent ≃ₗ[R] TensorProduct R Rₚ P.Cotangent := by
  classical
  let R := NumberField.RingOfIntegers L
  let Rₚ := Localization.AtPrime P
  let eLoc : P.Cotangent ≃ₗ[R] LocalizedModule P.primeCompl P.Cotangent :=
    number_localized_module (L := L) hq P
  let eTensor :
      LocalizedModule P.primeCompl P.Cotangent ≃ₗ[Rₚ] TensorProduct R Rₚ P.Cotangent :=
    LocalizedModule.equivTensorProduct P.primeCompl P.Cotangent
  exact eLoc.trans (eTensor.restrictScalars R)

lemma number_cotangent_localization
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (y : P.Cotangent) :
    let R := NumberField.RingOfIntegers L
    let Rₚ := Localization.AtPrime P
    cotangent_tensor_localization (L := L) hq P y =
      (1 : Rₚ) ⊗ₜ[R] y := by
  classical
  let R := NumberField.RingOfIntegers L
  let Rₚ := Localization.AtPrime P
  simp [
    cotangent_tensor_localization,
    cotangent_localized_module,
    Localization.mk_one_eq_algebraMap]

lemma number_field_cotangent
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : P.inertia (Gal(L/ℚ))) (x : P) :
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    field_inertia_cotangent (L := L) hq P σ (P.toCotangent x) =
      P.toCotangent
        ⟨(σ : Gal(L/ℚ)) • (x : NumberField.RingOfIntegers L),
          number_smul_prime (L := L) P σ x.property⟩ := by
  classical
  letI : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  change
    P.cotangentEquivIdeal.symm
        (field_cotangent_ideal (L := L) P σ
          (P.cotangentEquivIdeal (P.toCotangent x))) =
      P.toCotangent
        ⟨(σ : Gal(L/ℚ)) • (x : NumberField.RingOfIntegers L),
          number_smul_prime (L := L) P σ x.property⟩
  have hsource :
      P.cotangentEquivIdeal (P.toCotangent x) =
        ⟨Ideal.Quotient.mk (P ^ 2) (x : NumberField.RingOfIntegers L), by
          rw [Ideal.mk_mem_cotangentIdeal]
          exact x.property⟩ := by
    ext
    simp
  rw [hsource]
  rw [number_cotangent_mk
    (L := L) P σ (x : NumberField.RingOfIntegers L) x.property]
  exact
    Ideal.cotangentEquivIdeal_symm_apply
      (I := P) ((σ : Gal(L/ℚ)) • (x : NumberField.RingOfIntegers L))
      (number_smul_prime (L := L) P σ x.property)

lemma inertia_smul_sq
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ)))
    (r : NumberField.RingOfIntegers L) (x : P) :
    ((σ : Gal(L/ℚ)) • (r * (x : NumberField.RingOfIntegers L))) -
        r * ((σ : Gal(L/ℚ)) • (x : NumberField.RingOfIntegers L)) ∈ P ^ 2 := by
  classical
  have hσr :
      ((σ : Gal(L/ℚ)) • r) - r ∈ P := by
    exact number_smul_sub (L := L) P σ r
  have hσx :
      ((σ : Gal(L/ℚ)) • (x : NumberField.RingOfIntegers L)) ∈ P := by
    exact number_smul_prime (L := L) P σ x.property
  have hprod :
      (((σ : Gal(L/ℚ)) • r) - r) *
          ((σ : Gal(L/ℚ)) • (x : NumberField.RingOfIntegers L)) ∈ P ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hσr hσx
  convert hprod using 1
  rw [smul_mul']
  ring

lemma inertia_cotangent_smul
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : P.inertia (Gal(L/ℚ))) (r : NumberField.RingOfIntegers L) (x : P) :
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    field_inertia_cotangent (L := L) hq P σ
        ((algebraMap (NumberField.RingOfIntegers L) P.ResidueField r) • P.toCotangent x) =
      (algebraMap (NumberField.RingOfIntegers L) P.ResidueField r) •
        field_inertia_cotangent (L := L) hq P σ (P.toCotangent x) := by
  classical
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  rw [residue_smul_cotangent (L := L) hq P r x]
  rw [number_field_cotangent (L := L) hq P σ (r • x)]
  rw [number_field_cotangent (L := L) hq P σ x]
  rw [residue_smul_cotangent]
  apply (P.toCotangent_eq).mpr
  change
    ((σ : Gal(L/ℚ)) • (r * (x : NumberField.RingOfIntegers L))) -
        r * ((σ : Gal(L/ℚ)) • (x : NumberField.RingOfIntegers L)) ∈ P ^ 2
  exact inertia_smul_sq (L := L) P σ r x

lemma number_cotangent_smul
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : P.inertia (Gal(L/ℚ))) (a : P.ResidueField) (y : P.Cotangent) :
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    field_inertia_cotangent (L := L) hq P σ (a • y) =
      a • field_inertia_cotangent (L := L) hq P σ y := by
  classical
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  obtain ⟨r, rfl⟩ :=
    number_residue_surjective (L := L) hq P a
  obtain ⟨x, hx⟩ := P.toCotangent_surjective y
  rw [← hx]
  exact
    inertia_cotangent_smul
      (L := L) hq P σ r x

lemma cotangent_representation_smul
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    additiveRepresentationModule
      (K := P.ResidueField) (G0 := P.inertia (Gal(L/ℚ)))
      (V := P.cotangentIdeal)
      (number_residue_module (L := L) _hq P)
      (cotangent_add_representation (L := L) P) := by
  classical
  letI : AddCommGroup P.cotangentIdeal :=
    Submodule.addCommGroup P.cotangentIdeal
  let moduleInstIdeal : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) _hq P
  letI : Module P.ResidueField P.cotangentIdeal := moduleInstIdeal
  letI : SMul P.ResidueField P.cotangentIdeal := moduleInstIdeal.toSMul
  let moduleInstCotangent : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) _hq P
  letI : Module P.ResidueField P.Cotangent := moduleInstCotangent
  letI : SMul P.ResidueField P.Cotangent := moduleInstCotangent.toSMul
  change ∀ σ : P.inertia (Gal(L/ℚ)), ∀ a : P.ResidueField, ∀ z : P.cotangentIdeal,
    cotangent_add_representation (L := L) P σ (a • z) =
      a • cotangent_add_representation (L := L) P σ z
  intro σ a z
  let e : P.cotangentIdeal ≃ₗ[P.ResidueField] P.Cotangent :=
    number_cotangent_residue (L := L) _hq P
  apply e.injective
  calc
    e (cotangent_add_representation (L := L) P σ (a • z)) =
        field_inertia_cotangent (L := L) _hq P σ (e (a • z)) := by
          exact
            (number_inertia_cotangent
              (L := L) _hq P σ (a • z)).symm
    _ =
        field_inertia_cotangent (L := L) _hq P σ (a • e z) := by
          exact congrArg (field_inertia_cotangent (L := L) _hq P σ)
            (map_smul e a z)
    _ =
        a • field_inertia_cotangent (L := L) _hq P σ (e z) := by
          exact
            number_cotangent_smul
              (L := L) _hq P σ a (e z)
    _ =
        a • e (cotangent_add_representation (L := L) P σ z) := by
          exact congrArg (fun y => a • y)
            (number_inertia_cotangent
              (L := L) _hq P σ z)
    _ =
        e (a • cotangent_add_representation (L := L) P σ z) := by
          exact (map_smul e a
            (cotangent_add_representation (L := L) P σ z)).symm

lemma inertia_cotangent_representation
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    letI : Module P.ResidueField P.cotangentIdeal :=
      number_residue_module (L := L) hq P
    ∃ ρlin : P.inertia (Gal(L/ℚ)) →* P.cotangentIdeal ≃ₗ[P.ResidueField] P.cotangentIdeal,
      ρlin.ker =
        (cotangent_add_representation (L := L) P).ker := by
  letI : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  have hsmul :
      additiveRepresentationModule
        (K := P.ResidueField) (G0 := P.inertia (Gal(L/ℚ)))
        (V := P.cotangentIdeal)
        (number_residue_module (L := L) hq P)
        (cotangent_add_representation (L := L) P) := by
    exact
      cotangent_representation_smul
        (L := L) hq P
  exact
    additive_representation_linear
      (K := P.ResidueField) (G0 := P.inertia (Gal(L/ℚ)))
      (V := P.cotangentIdeal)
      (cotangent_add_representation (L := L) P)
      hsmul

lemma dimensional_module_spans
    {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (hfinrank : Module.finrank K V = 1) {v : V} (hv : v ≠ 0) :
    dimensionalSpansElement
      (K := K) (V := V) (inferInstance : Module K V) v := by
  intro w
  exact exists_smul_eq_of_finrank_eq_one (K := K) (V := V) hfinrank hv w

lemma dimensional_spans_finrank
    {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (hfinrank : Module.finrank K V = 1) :
    ∃ v : V,
      v ≠ 0 ∧
        dimensionalSpansElement
          (K := K) (V := V) (inferInstance : Module K V) v := by
  classical
  have hpos : 0 < Module.finrank K V := by
    rw [hfinrank]
    exact zero_lt_one
  haveI : Nontrivial V :=
    Module.nontrivial_of_finrank_pos (R := K) (M := V) hpos
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine ⟨v, ?_, ?_⟩
  · exact hv
  · exact dimensional_module_spans hfinrank hv

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

lemma finrank_semilinear_equiv
    {K K' V V' : Type*}
    [Semiring K] [Semiring K'] [AddCommMonoid V] [Module K V]
    [AddCommMonoid V'] [Module K' V']
    (σ : K ≃+* K') (e : V ≃ₛₗ[(σ : K →+* K')] V') :
    Module.finrank K V = Module.finrank K' V' := by
  unfold Module.finrank
  simpa only [Cardinal.toNat_lift] using
    congrArg Cardinal.toNat
      (lift_rank_eq_of_equiv_equiv (fun x : K => σ x) e.toAddEquiv σ.bijective
        (by
          intro r x
          exact e.map_smulₛₗ r x))

noncomputable def number_localization_prime
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    P.ResidueField ≃+* IsLocalRing.ResidueField (Localization.AtPrime P) := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  exact
    (idealResidueMaximal P).symm.trans
      (IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P))

lemma number_localization_algebra
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (r : NumberField.RingOfIntegers L) :
    let R := NumberField.RingOfIntegers L
    let Rₚ := Localization.AtPrime P
    number_localization_prime (L := L) hq P
        (algebraMap R P.ResidueField r) =
      algebraMap Rₚ (IsLocalRing.ResidueField Rₚ) (algebraMap R Rₚ r) := by
  classical
  let R := NumberField.RingOfIntegers L
  let Rₚ := Localization.AtPrime P
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  change
    number_localization_prime (L := L) hq P
        (algebraMap R P.ResidueField r) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal Rₚ) (algebraMap R Rₚ r)
  rw [number_localization_prime]
  change
    IsLocalization.AtPrime.equivQuotMaximalIdeal P Rₚ
        ((idealResidueMaximal P).symm
          (algebraMap R P.ResidueField r)) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal Rₚ) (algebraMap R Rₚ r)
  have hpre :
      (idealResidueMaximal P).symm
          (algebraMap R P.ResidueField r) =
        Ideal.Quotient.mk P r := by
    rw [RingEquiv.symm_apply_eq]
    change algebraMap R P.ResidueField r =
      algebraMap (R ⧸ P) P.ResidueField (Ideal.Quotient.mk P r)
    rfl
  rw [hpre]
  rfl

lemma smul_cotangent_space
    (R : Type*) [CommRing R] [IsLocalRing R]
    (x : R) (z : IsLocalRing.CotangentSpace R) :
    (algebraMap R (IsLocalRing.ResidueField R) x) • z = x • z := by
  exact algebraMap_smul (IsLocalRing.ResidueField R) x z

lemma number_localization_maximal
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    let Rₚ := Localization.AtPrime P
    P.map (algebraMap (NumberField.RingOfIntegers L) Rₚ) =
      IsLocalRing.maximalIdeal Rₚ := by
  classical
  let Rₚ := Localization.AtPrime P
  exact Localization.AtPrime.map_eq_maximalIdeal (I := P)

lemma localization_cotangent_space
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    let Rₚ := Localization.AtPrime P
    Module.finrank (IsLocalRing.ResidueField Rₚ) (IsLocalRing.CotangentSpace Rₚ) = 1 := by
  classical
  let Rₚ := Localization.AtPrime P
  have hp_ne_bot :
      Ideal.rationalPrimeIdeal q ≠ ⊥ := by
    exact rational_ne_bot hq
  have hP_ne_bot :
      P ≠ ⊥ := by
    exact Ideal.ne_bot_of_liesOver_of_ne_bot hp_ne_bot P
  haveI : IsDiscreteValuationRing Rₚ :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (NumberField.RingOfIntegers L) hP_ne_bot Rₚ
  exact IsLocalRing.finrank_CotangentSpace_eq_one Rₚ

noncomputable def idealCotangentLinear
    {R : Type*} [CommRing R] (I J : Ideal R) (h : I = J) :
    I.Cotangent ≃ₗ[R] J.Cotangent := by
  subst h
  exact LinearEquiv.refl R I.Cotangent

noncomputable def idealCotangentAlg
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (I : Ideal A) :
    I.Cotangent ≃ₗ[R] (I.map (e : A →+* B)).Cotangent := by
  classical
  let J : Ideal B := I.map (e : A →+* B)
  let f : I.Cotangent →ₗ[R] J.Cotangent :=
    Ideal.mapCotangent I J e.toAlgHom Ideal.le_comap_map
  have hJ_le : J ≤ I.comap (e.symm : B →+* A) := by
    rw [← Ideal.map_le_iff_le_comap]
    have hmap : J.map (e.symm : B →+* A) = I := by
      dsimp [J]
      rw [Ideal.map_map]
      have hcomp : (e.symm : B →+* A).comp (e : A →+* B) = RingHom.id A := by
        ext x
        exact e.left_inv x
      rw [hcomp, Ideal.map_id]
    exact hmap.le
  let g : J.Cotangent →ₗ[R] I.Cotangent :=
    Ideal.mapCotangent J I e.symm.toAlgHom hJ_le
  refine LinearEquiv.ofLinear f g ?_ ?_
  · ext x
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective J x
    simp [f, g, J, Ideal.mapCotangent_toCotangent]
  · ext y
    obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective I y
    simp [f, g, J, Ideal.mapCotangent_toCotangent]

noncomputable def localization_mapped_space
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    let R := NumberField.RingOfIntegers L
    let Rₚ := Localization.AtPrime P
    (P.map (algebraMap R Rₚ)).Cotangent ≃ₗ[Rₚ] IsLocalRing.CotangentSpace Rₚ := by
  classical
  let R := NumberField.RingOfIntegers L
  let Rₚ := Localization.AtPrime P
  exact
    idealCotangentLinear
      (P.map (algebraMap R Rₚ))
      (IsLocalRing.maximalIdeal Rₚ)
      (number_localization_maximal (L := L) hq P)

noncomputable def cotangent_localization_change
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    let Rₚ := Localization.AtPrime P;
    TensorProduct (NumberField.RingOfIntegers L) Rₚ P.Cotangent ≃ₗ[Rₚ]
      (P.map
        (Algebra.TensorProduct.includeRight.toRingHom :
          NumberField.RingOfIntegers L →+*
            TensorProduct
              (NumberField.RingOfIntegers L) Rₚ (NumberField.RingOfIntegers L))).Cotangent := by
  classical
  let R := NumberField.RingOfIntegers L
  let Rₚ := Localization.AtPrime P
  haveI : Module.Flat R Rₚ := IsLocalization.flat Rₚ P.primeCompl
  exact P.tensorCotangentEquiv R Rₚ

lemma localization_space_nonempty
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    let Rₚ := Localization.AtPrime P;
    Nonempty
      (TensorProduct (NumberField.RingOfIntegers L) Rₚ P.Cotangent ≃ₗ[Rₚ]
        IsLocalRing.CotangentSpace Rₚ) := by
  classical
  let R := NumberField.RingOfIntegers L
  let Rₚ := Localization.AtPrime P
  let eTensor :
      TensorProduct R Rₚ P.Cotangent ≃ₗ[Rₚ]
        (P.map
          (Algebra.TensorProduct.includeRight.toRingHom :
            R →+* TensorProduct R Rₚ R)).Cotangent :=
    cotangent_localization_change (L := L) hq P
  let eMax :
      (P.map (algebraMap R Rₚ)).Cotangent ≃ₗ[Rₚ] IsLocalRing.CotangentSpace Rₚ :=
    localization_mapped_space
      (L := L) hq P
  let eRid : TensorProduct R Rₚ R ≃ₐ[Rₚ] Rₚ :=
    Algebra.TensorProduct.rid R Rₚ Rₚ
  let J : Ideal (TensorProduct R Rₚ R) :=
    P.map (Algebra.TensorProduct.includeRight.toRingHom : R →+* TensorProduct R Rₚ R)
  let eRidCotangent : J.Cotangent ≃ₗ[Rₚ] (J.map (eRid : TensorProduct R Rₚ R →+* Rₚ)).Cotangent :=
    idealCotangentAlg eRid J
  have hRidMap :
      J.map (eRid : TensorProduct R Rₚ R →+* Rₚ) =
        P.map (algebraMap R Rₚ) := by
    dsimp [J, eRid]
    rw [Ideal.map_map]
    congr 1
    ext x
    simp [Algebra.TensorProduct.includeRight_apply, Algebra.smul_def]
  let eRidMap :
      (J.map (eRid : TensorProduct R Rₚ R →+* Rₚ)).Cotangent ≃ₗ[Rₚ]
        (P.map (algebraMap R Rₚ)).Cotangent :=
    idealCotangentLinear
      (J.map (eRid : TensorProduct R Rₚ R →+* Rₚ))
      (P.map (algebraMap R Rₚ))
      hRidMap
  exact ⟨eTensor.trans (eRidCotangent.trans (eRidMap.trans eMax))⟩

lemma localization_semilinear_nonempty
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (eBase :
      let Rₚ := Localization.AtPrime P;
      TensorProduct (NumberField.RingOfIntegers L) Rₚ P.Cotangent ≃ₗ[Rₚ]
        IsLocalRing.CotangentSpace Rₚ) :
    let Rₚ := Localization.AtPrime P;
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P;
    letI : Module (IsLocalRing.ResidueField Rₚ)
        (TensorProduct (NumberField.RingOfIntegers L) Rₚ P.Cotangent) :=
      eBase.toAddEquiv.module (IsLocalRing.ResidueField Rₚ);
    Nonempty
      (P.Cotangent ≃ₛₗ[
        (number_localization_prime (L := L) hq P :
          P.ResidueField →+* IsLocalRing.ResidueField Rₚ)]
        TensorProduct (NumberField.RingOfIntegers L) Rₚ P.Cotangent) := by
  classical
  let R := NumberField.RingOfIntegers L
  let Rₚ := Localization.AtPrime P
  let Kₚ := IsLocalRing.ResidueField Rₚ
  let σ : P.ResidueField ≃+* Kₚ :=
    number_localization_prime (L := L) hq P
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  letI : Module Kₚ (TensorProduct R Rₚ P.Cotangent) :=
    eBase.toAddEquiv.module Kₚ
  let eTensor : P.Cotangent ≃ₗ[R] TensorProduct R Rₚ P.Cotangent :=
    cotangent_tensor_localization (L := L) hq P
  let eSemilinear :
      P.Cotangent ≃ₛₗ[(σ : P.ResidueField →+* Kₚ)]
        TensorProduct R Rₚ P.Cotangent := {
    toFun := eTensor
    invFun := eTensor.symm
    left_inv := eTensor.left_inv
    right_inv := eTensor.right_inv
    map_add' := eTensor.map_add
    map_smul' := by
      intro a y
      obtain ⟨r, hr⟩ :=
        number_residue_surjective (L := L) hq P a
      rw [← hr]
      apply eBase.injective
      calc
        eBase
            (eTensor
              ((algebraMap R P.ResidueField r) • y)) =
            eBase (eTensor (r • y)) := by
              rw [number_smul_cotangent (L := L) hq P r y]
        _ = eBase (r • eTensor y) := by
              rw [map_smul]
        _ = eBase ((algebraMap R Rₚ r) • eTensor y) := by
              rw [algebraMap_smul Rₚ r (eTensor y)]
        _ = (algebraMap R Rₚ r) • eBase (eTensor y) := by
              rw [map_smul]
        _ =
            (algebraMap Rₚ Kₚ (algebraMap R Rₚ r)) •
              eBase (eTensor y) := by
              rw [smul_cotangent_space]
        _ =
            σ (algebraMap R P.ResidueField r) •
              eBase (eTensor y) := by
              rw [
                number_localization_algebra
                  (L := L) hq P r]
        _ =
            eBase
              (σ (algebraMap R P.ResidueField r) •
                eTensor y) := by
              simp [Equiv.smul_def]
  }
  exact ⟨eSemilinear⟩

lemma localization_space_semilinear
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    let Rₚ := Localization.AtPrime P
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    Nonempty
      (P.Cotangent ≃ₛₗ[
        (number_localization_prime (L := L) hq P :
          P.ResidueField →+* IsLocalRing.ResidueField Rₚ)]
        IsLocalRing.CotangentSpace Rₚ) := by
  classical
  let R := NumberField.RingOfIntegers L
  let Rₚ := Localization.AtPrime P
  obtain ⟨eBase⟩ :=
    localization_space_nonempty
      (L := L) hq P
  letI : Module (IsLocalRing.ResidueField Rₚ) (TensorProduct R Rₚ P.Cotangent) :=
    eBase.toAddEquiv.module (IsLocalRing.ResidueField Rₚ)
  obtain ⟨eSource⟩ :=
    localization_semilinear_nonempty
      (L := L) hq P eBase
  let eBaseResidue :
      TensorProduct R Rₚ P.Cotangent ≃ₗ[IsLocalRing.ResidueField Rₚ]
        IsLocalRing.CotangentSpace Rₚ :=
    eBase.toAddEquiv.linearEquiv (IsLocalRing.ResidueField Rₚ)
  exact ⟨eSource.trans eBaseResidue⟩

lemma space_semilinear_nonempty
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    let Rₚ := Localization.AtPrime P
    letI : Module P.ResidueField P.cotangentIdeal :=
      number_residue_module (L := L) hq P
    Nonempty
      (P.cotangentIdeal ≃ₛₗ[
        (number_localization_prime (L := L) hq P :
          P.ResidueField →+* IsLocalRing.ResidueField Rₚ)]
        IsLocalRing.CotangentSpace Rₚ) := by
  classical
  let Rₚ := Localization.AtPrime P
  letI : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  obtain ⟨eCotangent⟩ :=
    localization_space_semilinear
      (L := L) hq P
  let eIdeal : P.cotangentIdeal ≃ₗ[P.ResidueField] P.Cotangent :=
    number_cotangent_residue (L := L) hq P
  exact ⟨eIdeal.trans eCotangent⟩

lemma cotangent_localization_space
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    let Rₚ := Localization.AtPrime P
    letI : Module P.ResidueField P.cotangentIdeal :=
      number_residue_module (L := L) hq P
    Module.finrank P.ResidueField P.cotangentIdeal =
      Module.finrank (IsLocalRing.ResidueField Rₚ) (IsLocalRing.CotangentSpace Rₚ) := by
  classical
  let Rₚ := Localization.AtPrime P
  letI : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  let σ : P.ResidueField ≃+* IsLocalRing.ResidueField Rₚ :=
    number_localization_prime (L := L) hq P
  obtain ⟨e⟩ :=
    space_semilinear_nonempty
      (L := L) hq P
  exact finrank_semilinear_equiv σ e

lemma cotangent_residue_finrank
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    letI : Module P.ResidueField P.cotangentIdeal :=
      number_residue_module (L := L) hq P
    Module.finrank P.ResidueField P.cotangentIdeal ≤ 1 := by
  classical
  let Rₚ := Localization.AtPrime P
  letI : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  have htransport :
      Module.finrank P.ResidueField P.cotangentIdeal =
        Module.finrank (IsLocalRing.ResidueField Rₚ) (IsLocalRing.CotangentSpace Rₚ) := by
    exact
      cotangent_localization_space
        (L := L) hq P
  have hlocal :
      Module.finrank (IsLocalRing.ResidueField Rₚ) (IsLocalRing.CotangentSpace Rₚ) = 1 := by
    exact localization_cotangent_space (L := L) hq P
  rw [htransport, hlocal]

lemma number_cotangent_pos
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    letI : Module P.ResidueField P.cotangentIdeal :=
      number_residue_module (L := L) hq P
    0 < Module.finrank P.ResidueField P.cotangentIdeal := by
  classical
  let Rₚ := Localization.AtPrime P
  letI : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  have htransport :
      Module.finrank P.ResidueField P.cotangentIdeal =
        Module.finrank (IsLocalRing.ResidueField Rₚ) (IsLocalRing.CotangentSpace Rₚ) := by
    exact
      cotangent_localization_space
        (L := L) hq P
  have hlocal :
      Module.finrank (IsLocalRing.ResidueField Rₚ) (IsLocalRing.CotangentSpace Rₚ) = 1 := by
    exact localization_cotangent_space (L := L) hq P
  rw [htransport, hlocal]
  exact zero_lt_one

lemma number_cotangent_finrank
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    letI : Module P.ResidueField P.cotangentIdeal :=
      number_residue_module (L := L) hq P
    Module.finrank P.ResidueField P.cotangentIdeal = 1 := by
  classical
  letI : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  have hle :
      Module.finrank P.ResidueField P.cotangentIdeal ≤ 1 := by
    exact cotangent_residue_finrank (L := L) hq P
  have hpos :
      0 < Module.finrank P.ResidueField P.cotangentIdeal := by
    exact number_cotangent_pos (L := L) hq P
  exact le_antisymm hle (Nat.succ_le_of_lt hpos)

lemma cotangent_residue_generator
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∃ v : P.cotangentIdeal,
      v ≠ 0 ∧
        dimensionalSpansElement
          (K := P.ResidueField) (V := P.cotangentIdeal)
          (number_residue_module (L := L) _hq P) v := by
  classical
  letI : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) _hq P
  have hfinrank :
      Module.finrank P.ResidueField P.cotangentIdeal = 1 := by
    exact number_cotangent_finrank (L := L) _hq P
  exact
    dimensional_spans_finrank
      (K := P.ResidueField) (V := P.cotangentIdeal) hfinrank

lemma cotangent_line_representation
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∃ moduleInst : Module P.ResidueField P.cotangentIdeal,
      letI : Module P.ResidueField P.cotangentIdeal := moduleInst
      ∃ ρlin : P.inertia (Gal(L/ℚ)) →* P.cotangentIdeal ≃ₗ[P.ResidueField] P.cotangentIdeal,
        ρlin.ker =
            (cotangent_add_representation (L := L) P).ker ∧
          ∃ v : P.cotangentIdeal,
            v ≠ 0 ∧
              dimensionalSpansElement
                (K := P.ResidueField) (V := P.cotangentIdeal) moduleInst v := by
  let moduleInst : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  refine ⟨moduleInst, ?_⟩
  letI : Module P.ResidueField P.cotangentIdeal := moduleInst
  obtain ⟨ρlin, hρlinKer⟩ :=
    inertia_cotangent_representation
      (L := L) hq P
  obtain ⟨v, hv_ne_zero, hv_span⟩ :=
    cotangent_residue_generator
      (L := L) hq P
  exact ⟨ρlin, hρlinKer, v, hv_ne_zero, hv_span⟩

lemma tame_cotangent_representation
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∃ χ : P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ,
      χ.ker =
        (cotangent_add_representation (L := L) P).ker := by
  obtain ⟨moduleInst, hdata⟩ :=
    cotangent_line_representation (L := L) hq P
  letI : Module P.ResidueField P.cotangentIdeal := moduleInst
  obtain ⟨ρlin, hρlinKer, v, hv_ne_zero, hv_span⟩ := hdata
  obtain ⟨χ, hχKer⟩ :=
    dimensional_spans_element
      (K := P.ResidueField) (G0 := P.inertia (Gal(L/ℚ)))
      (V := P.cotangentIdeal) ρlin v hv_ne_zero hv_span
  refine ⟨χ, ?_⟩
  rw [hχKer, hρlinKer]

lemma tame_inertia_cotangent
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∃ χ : P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ,
      ∀ σ : P.inertia (Gal(L/ℚ)),
        σ ∈ χ.ker ↔
          ∀ z : P.cotangentIdeal,
            field_cotangent_ideal (L := L) P σ z = z := by
  obtain ⟨χ, hχKer⟩ :=
    tame_cotangent_representation
      (L := L) hq P
  refine ⟨χ, ?_⟩
  intro σ
  rw [hχKer]
  exact
    cotangent_representation_ker
      (L := L) P σ

lemma inertia_cotangent_wild
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : P.inertia (Gal(L/ℚ))) :
    (∀ z : P.cotangentIdeal,
        field_cotangent_ideal (L := L) P σ z = z) ↔
      σ ∈ number_wild_subgroup (L := L) P := by
  constructor
  · intro hσ
    have hKer :
        σ ∈ (cotangent_add_representation (L := L) P).ker := by
      exact
        (cotangent_representation_ker
          (L := L) P σ).2 hσ
    exact
      (number_cotangent_wild
        (L := L) hq P) hKer
  · intro hσ
    have hKer :
        σ ∈ (cotangent_add_representation (L := L) P).ker := by
      exact
        wild_cotangent_representation
          (L := L) P hσ
    exact
      (cotangent_representation_ker
        (L := L) P σ).1 hKer

lemma tame_cotangent_wild
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (χ : P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ)
    (hχ : ∀ σ : P.inertia (Gal(L/ℚ)),
      σ ∈ χ.ker ↔
        ∀ z : P.cotangentIdeal,
          field_cotangent_ideal (L := L) P σ z = z) :
    χ.ker = number_wild_subgroup (L := L) P := by
  ext σ
  constructor
  · intro hσ
    have hfixed :
        ∀ z : P.cotangentIdeal,
          field_cotangent_ideal (L := L) P σ z = z := by
      exact (hχ σ).1 hσ
    exact
      (inertia_cotangent_wild
        (L := L) hq P σ).1 hfixed
  · intro hσ
    have hfixed :
        ∀ z : P.cotangentIdeal,
          field_cotangent_ideal (L := L) P σ z = z := by
      exact
        (inertia_cotangent_wild
          (L := L) hq P σ).2 hσ
    exact (hχ σ).2 hfixed

lemma tame_uniformizer_wild
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∃ χ : P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ,
      χ.ker = number_wild_subgroup (L := L) P := by
  obtain ⟨χ, hχ⟩ :=
    tame_inertia_cotangent
      (L := L) hq P
  refine ⟨χ, ?_⟩
  exact
    tame_cotangent_wild
      (L := L) hq P χ hχ

lemma rational_nat_cast {q n : ℕ} :
    (n : ℤ) ∈ Ideal.rationalPrimeIdeal q ↔ q ∣ n := by
  rw [Ideal.rationalPrimeIdeal]
  rw [Ideal.mem_span_singleton]
  exact Int.natCast_dvd_natCast

lemma number_rational_lies
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    (q : ℕ)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    (q : NumberField.RingOfIntegers L) ∈ P := by
  have hqInt :
      (q : ℤ) ∈ Ideal.rationalPrimeIdeal q := by
    exact rational_nat_cast.mpr dvd_rfl
  have hqAlg :
      algebraMap ℤ (NumberField.RingOfIntegers L) (q : ℤ) ∈ P := by
    exact
      (Ideal.mem_of_liesOver
        (P := P) (p := Ideal.rationalPrimeIdeal q) (x := (q : ℤ))).1 hqInt
  simpa [Int.cast_natCast] using hqAlg

lemma number_cast_zero
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q n : ℕ}
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    (n : P.ResidueField) = 0 ↔ q ∣ n := by
  have hInt :
      algebraMap ℤ P.ResidueField (n : ℤ) = 0 ↔ q ∣ n := by
    rw [IsScalarTower.algebraMap_apply
      ℤ (NumberField.RingOfIntegers L) P.ResidueField]
    rw [Ideal.algebraMap_residueField_eq_zero]
    rw [← Ideal.mem_of_liesOver
      (P := P) (p := Ideal.rationalPrimeIdeal q) (x := (n : ℤ))]
    exact rational_nat_cast
  simpa [Int.cast_natCast] using hInt

lemma number_nat_cast
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q n : ℕ}
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    (n : NumberField.RingOfIntegers L) ∈ P ↔ q ∣ n := by
  have hmem :
      algebraMap ℤ (NumberField.RingOfIntegers L) (n : ℤ) ∈ P ↔
        (n : ℤ) ∈ Ideal.rationalPrimeIdeal q := by
    exact
      (Ideal.mem_of_liesOver
        (P := P) (p := Ideal.rationalPrimeIdeal q) (x := (n : ℤ))).symm
  simpa [Int.cast_natCast] using hmem.trans rational_nat_cast

lemma number_cast_not
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q ℓ : ℕ} (hq : Nat.Prime q) (hℓ : Nat.Prime ℓ) (hℓ_ne_q : ℓ ≠ q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    (ℓ : NumberField.RingOfIntegers L) ∉ P := by
  rw [number_nat_cast (L := L) (q := q) (n := ℓ) P]
  intro hdiv
  have hq_eq_l : q = ℓ := (Nat.prime_dvd_prime_iff_eq hq hℓ).1 hdiv
  exact hℓ_ne_q hq_eq_l.symm

lemma number_ne_cast
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q ℓ : ℕ} (hq : Nat.Prime q) (hℓ : Nat.Prime ℓ) (hℓ_ne_q : ℓ ≠ q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    (ℓ : P.ResidueField) ≠ 0 := by
  intro hzero
  have hdiv : q ∣ ℓ := by
    exact
      (number_cast_zero
        (L := L) (q := q) (n := ℓ) P).1 hzero
  have hq_eq_l : q = ℓ := (Nat.prime_dvd_prime_iff_eq hq hℓ).1 hdiv
  exact hℓ_ne_q hq_eq_l.symm

noncomputable def number_ne_unit
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q ℓ : ℕ} (hq : Nat.Prime q) (hℓ : Nat.Prime ℓ) (hℓ_ne_q : ℓ ≠ q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    P.ResidueFieldˣ :=
  Units.mk0 (ℓ : P.ResidueField)
    (number_ne_cast
      (L := L) hq hℓ hℓ_ne_q P)

lemma number_ne_coe
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q ℓ : ℕ} (hq : Nat.Prime q) (hℓ : Nat.Prime ℓ) (hℓ_ne_q : ℓ ≠ q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ((number_ne_unit
      (L := L) hq hℓ hℓ_ne_q P : P.ResidueFieldˣ) : P.ResidueField) = ℓ := by
  simp [number_ne_unit]

lemma number_localization_unit
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q ℓ : ℕ} (hq : Nat.Prime q) (hℓ : Nat.Prime ℓ) (hℓ_ne_q : ℓ ≠ q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    IsUnit
      (algebraMap (NumberField.RingOfIntegers L) (Localization.AtPrime P)
        (ℓ : NumberField.RingOfIntegers L)) := by
  let R := NumberField.RingOfIntegers L
  have hnot :
      (ℓ : R) ∉ P := by
    exact number_cast_not (L := L) hq hℓ hℓ_ne_q P
  exact
    IsLocalization.map_units (M := P.primeCompl)
      (Localization.AtPrime P) ⟨(ℓ : R), hnot⟩

lemma residue_char_p
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    CharP P.ResidueField q where
  cast_eq_zero_iff n :=
    number_cast_zero (L := L) (q := q) (n := n) P

lemma number_additive_p
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    IsPGroup q (Multiplicative P.ResidueField) := by
  haveI : CharP P.ResidueField q :=
    residue_char_p (L := L) hq P
  letI : Algebra (ZMod q) P.ResidueField :=
    ZMod.algebra P.ResidueField q
  exact ZModModule.isPGroup_multiplicative

lemma cotangent_cast_nsmul
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ}
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (z : P.cotangentIdeal) :
    q • z = 0 := by
  classical
  have hqP :
      (q : NumberField.RingOfIntegers L) ∈ P := by
    exact number_rational_lies (L := L) q P
  ext
  change q • (z : NumberField.RingOfIntegers L ⧸ P ^ 2) = 0
  obtain ⟨x, hxz⟩ :=
    Ideal.Quotient.mk_surjective
      (z : NumberField.RingOfIntegers L ⧸ P ^ 2)
  rw [← hxz]
  have hxP : x ∈ P := by
    have hzMem : (z : NumberField.RingOfIntegers L ⧸ P ^ 2) ∈
        P.cotangentIdeal := z.property
    rw [← hxz] at hzMem
    rwa [Ideal.mk_mem_cotangentIdeal] at hzMem
  have hmem :
      q • x ∈ P ^ 2 := by
    rw [nsmul_eq_mul]
    simpa [pow_two] using Ideal.mul_mem_mul hqP hxP
  have hzero :
      Ideal.Quotient.mk (P ^ 2) (q • x) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  simpa using hzero

lemma number_cotangent_additive
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    IsPGroup q (Multiplicative P.cotangentIdeal) := by
  have hkill :
      ∀ z : P.cotangentIdeal, q • z = 0 := by
    intro z
    exact cotangent_cast_nsmul (L := L) (q := q) P z
  letI : Module (ZMod q) P.cotangentIdeal :=
    AddCommGroup.zmodModule (n := q) hkill
  exact ZModModule.isPGroup_multiplicative

lemma number_i_inf
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] :
    (⨅ n : ℕ, P ^ n) = (⊥ : Ideal (NumberField.RingOfIntegers L)) := by
  exact Ideal.iInf_pow_eq_bot_of_isDomain (I := P) (Ideal.IsPrime.ne_top inferInstance)

lemma all_prime_powers
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime]
    {x : NumberField.RingOfIntegers L}
    (hx : ∀ n : ℕ, x ∈ P ^ n) :
    x = 0 := by
  have hx_iInf :
      x ∈ (⨅ n : ℕ, P ^ n) := by
    exact Ideal.mem_iInf.mpr hx
  have hx_bot :
      x ∈ (⊥ : Ideal (NumberField.RingOfIntegers L)) := by
    simpa [number_i_inf (L := L) P] using hx_iInf
  simpa using hx_bot

lemma number_all_powers
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime]
    (σ : P.inertia (Gal(L/ℚ)))
    (hσ : ∀ n : ℕ, ∀ x : NumberField.RingOfIntegers L,
      ((σ : Gal(L/ℚ)) • x) - x ∈ P ^ n)
    (x : NumberField.RingOfIntegers L) :
    ((σ : Gal(L/ℚ)) • x) = x := by
  have hdiff_zero :
      ((σ : Gal(L/ℚ)) • x) - x = 0 := by
    exact
      all_prime_powers (L := L) P
        (x := ((σ : Gal(L/ℚ)) • x) - x) (fun n => hσ n x)
  exact sub_eq_zero.mp hdiff_zero

lemma number_inertia_forall
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ)))
    (hσ : ∀ x : NumberField.RingOfIntegers L,
      ((σ : Gal(L/ℚ)) • x) = x)
    (i : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers L)) :
    ((σ : Gal(L/ℚ)) : L ≃ₐ[ℚ] L) (NumberField.integralBasis L i) =
      NumberField.integralBasis L i := by
  have hbasis_fixed :
      ((σ : Gal(L/ℚ)) • NumberField.RingOfIntegers.basis L i) =
        NumberField.RingOfIntegers.basis L i := by
    exact hσ (NumberField.RingOfIntegers.basis L i)
  have hbasis_fixed_field :
      (((σ : Gal(L/ℚ)) • NumberField.RingOfIntegers.basis L i :
          NumberField.RingOfIntegers L) : L) =
        (NumberField.RingOfIntegers.basis L i : L) := by
    exact congr_arg (fun x : NumberField.RingOfIntegers L => (x : L)) hbasis_fixed
  rw [NumberField.integralBasis_apply]
  change
    (((σ : Gal(L/ℚ)) • NumberField.RingOfIntegers.basis L i :
        NumberField.RingOfIntegers L) : L) =
      (NumberField.RingOfIntegers.basis L i : L)
  exact hbasis_fixed_field

lemma number_refl_fixed
    (L : Type*) [Field L] [NumberField L]
    (e : L ≃+* L)
    (he : ∀ i : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers L),
      e (NumberField.integralBasis L i) = NumberField.integralBasis L i) :
    e = RingEquiv.refl L := by
  let eLin : L →ₗ[ℚ] L :=
    { toFun := fun x => e x
      map_add' := by
        intro x y
        exact e.map_add x y
      map_smul' := by
        intro c x
        have hc : e (algebraMap ℚ L c) = algebraMap ℚ L c := by
          exact map_ratCast e c
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, hc]
        rfl }
  have hlin : eLin = LinearMap.id := by
    exact (NumberField.integralBasis L).ext (f₁ := eLin) (f₂ := LinearMap.id) he
  ext x
  have hx := congr_arg (fun f : L →ₗ[ℚ] L => f x) hlin
  simpa [eLin] using hx

lemma number_inertia_fixed
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ)))
    (hσ : ∀ i : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers L),
      ((σ : Gal(L/ℚ)) : L ≃ₐ[ℚ] L) (NumberField.integralBasis L i) =
        NumberField.integralBasis L i) :
    σ = 1 := by
  have hring :
      ((σ : Gal(L/ℚ)) : L ≃ₐ[ℚ] L).toRingEquiv = RingEquiv.refl L := by
    refine
      number_refl_fixed (L := L)
        ((σ : Gal(L/ℚ)) : L ≃ₐ[ℚ] L).toRingEquiv ?_
    intro i
    exact hσ i
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  have hx := congr_arg (fun e : L ≃+* L => e x) hring
  simpa using hx

lemma number_forall_fixed
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ)))
    (hσ : ∀ x : NumberField.RingOfIntegers L,
      ((σ : Gal(L/ℚ)) • x) = x) :
    σ = 1 := by
  refine number_inertia_fixed (L := L) P σ ?_
  intro i
  exact
    number_inertia_forall
      (L := L) P σ hσ i

lemma inertia_all_powers
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : P.inertia (Gal(L/ℚ)))
    (hσ : ∀ n : ℕ, ∀ x : NumberField.RingOfIntegers L,
      ((σ : Gal(L/ℚ)) • x) - x ∈ P ^ n) :
    σ = 1 := by
  refine number_forall_fixed (L := L) P σ ?_
  intro x
  exact number_all_powers
    (L := L) P σ hσ x

lemma number_wild_inertia
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {ℓ : ℕ}
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : number_wild_subgroup (L := L) P)
    (hσ_order : orderOf σ = ℓ) :
    ((σ : P.inertia (Gal(L/ℚ))) ^ ℓ) = 1 := by
  have hpow_subgroup : σ ^ ℓ = 1 := by
    have hpow_order : σ ^ orderOf σ = 1 := by
      exact pow_orderOf_eq_one σ
    rw [hσ_order] at hpow_order
    exact hpow_order
  exact
    congr_arg
      (fun τ : number_wild_subgroup (L := L) P =>
        (τ : P.inertia (Gal(L/ℚ))))
      hpow_subgroup

lemma wild_iterate_smul
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {ℓ : ℕ}
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : number_wild_subgroup (L := L) P)
    (hσ_order : orderOf σ = ℓ)
    (x : NumberField.RingOfIntegers L) :
    (((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) ^ ℓ) • x = x := by
  have hpow_inertia :
      ((σ : P.inertia (Gal(L/ℚ))) ^ ℓ) = 1 := by
    exact
      number_wild_inertia
        (L := L) P σ hσ_order
  have hpow_gal :
      (((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) ^ ℓ) = 1 := by
    simpa using
      congr_arg
        (fun τ : P.inertia (Gal(L/ℚ)) => (τ : Gal(L/ℚ)))
        hpow_inertia
  simp [hpow_gal]

lemma smul_sub_range
    {gtype : Type*} {atype : Type*}
    [Group gtype] [AddCommGroup atype] [DistribMulAction gtype atype]
    (g : gtype) (n : ℕ) (x : atype) :
    (g ^ n) • x - x =
      ∑ i ∈ Finset.range n, (g ^ i) • (g • x - x) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        (g ^ (n + 1)) • x - x =
            ((g ^ n) • x - x) + (g ^ n) • (g • x - x) := by
          rw [pow_succ, mul_smul, smul_sub]
          abel
        _ = (∑ i ∈ Finset.range n, (g ^ i) • (g • x - x)) +
            (g ^ n) • (g • x - x) := by
          rw [ih]
        _ = ∑ i ∈ Finset.range (n + 1), (g ^ i) • (g • x - x) := by
          exact (Finset.sum_range_succ (fun i => (g ^ i) • (g • x - x)) n).symm

lemma ideal_cancel_not
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : Ideal R) [P.IsPrime] {a x : R} {n : ℕ}
    (ha : a ∉ P) (hax : a * x ∈ P ^ n) :
    x ∈ P ^ n := by
  exact (Ideal.IsPrime.mul_mem_pow P hax).resolve_left ha

lemma inertia_smul_pow
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (n : ℕ) :
    (σ : Gal(L/ℚ)) • (P ^ n) = P ^ n := by
  classical
  have hStab :
      (σ : Gal(L/ℚ)) • P = P := by
    exact field_inertia_stabilizer (L := L) P σ
  calc
    (σ : Gal(L/ℚ)) • (P ^ n) = ((σ : Gal(L/ℚ)) • P) ^ n := by
      simp [smul_pow']
    _ = P ^ n := by
      rw [hStab]

lemma number_smul_pow
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (n : ℕ)
    {x : NumberField.RingOfIntegers L}
    (hx : x ∈ P ^ n) :
    ((σ : Gal(L/ℚ)) • x) ∈ P ^ n := by
  classical
  have hMem :
      ((σ : Gal(L/ℚ)) • x) ∈ (σ : Gal(L/ℚ)) • (P ^ n) := by
    exact Ideal.smul_mem_pointwise_smul (σ : Gal(L/ℚ)) x (P ^ n) hx
  simpa [inertia_smul_pow (L := L) P σ n] using hMem

lemma number_ne_pow
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    {q ℓ : ℕ} (hq : Nat.Prime q) (hℓ : Nat.Prime ℓ) (hℓ_ne_q : ℓ ≠ q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    {n : ℕ} {x : NumberField.RingOfIntegers L}
    (hmem : (ℓ : NumberField.RingOfIntegers L) * x ∈ P ^ n) :
    x ∈ P ^ n := by
  have hnot :
      (ℓ : NumberField.RingOfIntegers L) ∉ P := by
    exact number_cast_not (L := L) hq hℓ hℓ_ne_q P
  exact ideal_cancel_not P hnot hmem

lemma number_wild_zero
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {ℓ : ℕ}
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : number_wild_subgroup (L := L) P)
    (hσ_order : orderOf σ = ℓ)
    (x : NumberField.RingOfIntegers L) :
    let τ : Gal(L/ℚ) := ((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ))
    (∑ i ∈ Finset.range ℓ, ((τ ^ i) • ((τ • x) - x))) = 0 := by
  let τ : Gal(L/ℚ) := ((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ))
  have htel :
      ((τ ^ ℓ) • x) - x =
        ∑ i ∈ Finset.range ℓ, ((τ ^ i) • ((τ • x) - x)) := by
    exact smul_sub_range τ ℓ x
  have hpowx :
      ((τ ^ ℓ) • x) = x := by
    simpa [τ] using
      wild_iterate_smul
        (L := L) P σ hσ_order x
  have hleft :
      ((τ ^ ℓ) • x) - x = 0 := by
    simp [hpowx]
  rw [hleft] at htel
  simpa [τ] using htel.symm

lemma inertia_smul_pred
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ)))
    {n m : ℕ}
    (hcong : ∀ x : NumberField.RingOfIntegers L,
      ((σ : Gal(L/ℚ)) • x) - x ∈ P ^ n)
    {y : NumberField.RingOfIntegers L}
    (hy : y ∈ P ^ m) (hm : 0 < m) :
    ((σ : Gal(L/ℚ)) • y) - y ∈ P ^ (n + m - 1) := by
  let τ : Gal(L/ℚ) := (σ : Gal(L/ℚ))
  change τ • y - y ∈ P ^ (n + m - 1)
  suffices hmain : ∀ {m : ℕ} {y : NumberField.RingOfIntegers L},
      y ∈ P ^ m → 0 < m → τ • y - y ∈ P ^ (n + m - 1) from
    hmain hy hm
  intro m y hy
  refine Submodule.pow_induction_on_left' (M := P)
    (C := fun i z _hz => 0 < i → τ • z - z ∈ P ^ (n + i - 1)) ?base ?add ?mul hy
  · intro r hpos
    omega
  · intro x z i _hx _hz hxprop hzprop hpos
    rw [smul_add, add_sub_add_comm]
    exact (P ^ (n + i - 1)).add_mem (hxprop hpos) (hzprop hpos)
  · intro a ha i z hz hzprop _hpos_succ
    cases i with
    | zero =>
        simpa [τ] using hcong (a * z)
    | succ i =>
        have hpos : 0 < i.succ := Nat.succ_pos i
        have hdiff_z : τ • z - z ∈ P ^ (n + i) := by
          simpa using hzprop hpos
        have hτaP : τ • a ∈ P := by
          exact number_smul_prime (L := L) P σ ha
        have hterm1 : (τ • a) * (τ • z - z) ∈ P ^ (n + i.succ) := by
          have hmul : (τ • a) * (τ • z - z) ∈ P * P ^ (n + i) := by
            exact Ideal.mul_mem_mul hτaP hdiff_z
          have hpoweq : P ^ (n + i.succ) = P * P ^ (n + i) := by
            rw [show n + i.succ = (n + i) + 1 by omega, pow_succ']
          rwa [hpoweq]
        have hterm2 : (τ • a - a) * z ∈ P ^ (n + i.succ) := by
          have hdiff_a : τ • a - a ∈ P ^ n := by
            simpa [τ] using hcong a
          have hmul : (τ • a - a) * z ∈ P ^ n * P ^ i.succ := by
            exact Ideal.mul_mem_mul hdiff_a hz
          simpa [pow_add] using hmul
        have hdecomp :
            τ • (a * z) - a * z =
              (τ • a) * (τ • z - z) + (τ • a - a) * z := by
          rw [smul_mul']
          ring
        rw [hdecomp]
        exact (P ^ (n + i.succ)).add_mem hterm1 hterm2

lemma number_inertia_smul
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ))) (m : ℕ)
    {y : NumberField.RingOfIntegers L}
    (hy : y ∈ P ^ m) (k : ℕ) :
    (((σ : Gal(L/ℚ)) ^ k) • y) ∈ P ^ m := by
  let τ : Gal(L/ℚ) := (σ : Gal(L/ℚ))
  change (τ ^ k) • y ∈ P ^ m
  induction k with
  | zero =>
      simpa using hy
  | succ k ih =>
      have hmem :
          τ • ((τ ^ k) • y) ∈ P ^ m := by
        exact number_smul_pow (L := L) P σ m ih
      simpa [τ, pow_succ', mul_smul] using hmem

lemma number_smul_pred
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : P.inertia (Gal(L/ℚ)))
    {n m : ℕ}
    (hcong : ∀ x : NumberField.RingOfIntegers L,
      ((σ : Gal(L/ℚ)) • x) - x ∈ P ^ n)
    {y : NumberField.RingOfIntegers L}
    (hy : y ∈ P ^ m) (hm : 0 < m) (k : ℕ) :
    (((σ : Gal(L/ℚ)) ^ k) • y) - y ∈ P ^ (n + m - 1) := by
  let τ : Gal(L/ℚ) := (σ : Gal(L/ℚ))
  change (τ ^ k) • y - y ∈ P ^ (n + m - 1)
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hpow_mem : (τ ^ k) • y ∈ P ^ m := by
        simpa [τ] using
          number_inertia_smul (L := L) P σ m hy k
      have hstep :
          τ • ((τ ^ k) • y) - ((τ ^ k) • y) ∈ P ^ (n + m - 1) := by
        simpa [τ] using
          inertia_smul_pred
            (L := L) P σ hcong hpow_mem hm
      have hdecomp :
          (τ ^ (k + 1)) • y - y =
            (τ • ((τ ^ k) • y) - ((τ ^ k) • y)) + ((τ ^ k) • y - y) := by
        rw [pow_succ', mul_smul]
        abel
      rw [hdecomp]
      exact (P ^ (n + m - 1)).add_mem hstep ih

lemma number_wild_congruence
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q ℓ : ℕ} (hq : Nat.Prime q) (hℓ : Nat.Prime ℓ) (hℓ_ne_q : ℓ ≠ q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : number_wild_subgroup (L := L) P)
    (hσ_order : orderOf σ = ℓ)
    {n : ℕ} (hn : 2 ≤ n)
    (hcong : ∀ x : NumberField.RingOfIntegers L,
      (((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) - x ∈ P ^ n) :
    ∀ x : NumberField.RingOfIntegers L,
      (((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) - x ∈ P ^ (n + 1) := by
  intro x
  let τ : Gal(L/ℚ) := ((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ))
  let d : NumberField.RingOfIntegers L := τ • x - x
  have hd : d ∈ P ^ n := by
    simpa [τ, d] using hcong x
  have hn_pos : 0 < n := by
    omega
  have htranslate :
      ∀ i ∈ Finset.range ℓ, (τ ^ i) • d - d ∈ P ^ (n + 1) := by
    intro i _hi
    have hhigh :
        (τ ^ i) • d - d ∈ P ^ (n + n - 1) := by
      simpa [τ] using
        number_smul_pred
          (L := L) P (σ : P.inertia (Gal(L/ℚ))) hcong hd hn_pos i
    exact Ideal.pow_le_pow_right (by omega : n + 1 ≤ n + n - 1) hhigh
  have horbit :
      (∑ i ∈ Finset.range ℓ, (τ ^ i) • d) = 0 := by
    simpa [τ, d] using
      number_wild_zero
        (L := L) P σ hσ_order x
  have hsum_sub :
      (∑ i ∈ Finset.range ℓ, (τ ^ i) • d) -
          (∑ i ∈ Finset.range ℓ, d) ∈ P ^ (n + 1) := by
    rw [← Finset.sum_sub_distrib]
    exact Ideal.sum_mem (P ^ (n + 1)) htranslate
  have hsum_const :
      (∑ _i ∈ Finset.range ℓ, d) =
        (ℓ : NumberField.RingOfIntegers L) * d := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hneg :
      -((ℓ : NumberField.RingOfIntegers L) * d) ∈ P ^ (n + 1) := by
    simpa [horbit, hsum_const] using hsum_sub
  have hlmul :
      (ℓ : NumberField.RingOfIntegers L) * d ∈ P ^ (n + 1) := by
    simpa using (P ^ (n + 1)).neg_mem hneg
  exact
    number_ne_pow
      (L := L) hq hℓ hℓ_ne_q P hlmul

lemma wild_all_powers
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : number_wild_subgroup (L := L) P)
    (hstep : ∀ {n : ℕ}, 2 ≤ n →
      (∀ x : NumberField.RingOfIntegers L,
        (((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) - x ∈ P ^ n) →
      ∀ x : NumberField.RingOfIntegers L,
        (((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) - x ∈ P ^ (n + 1)) :
    ∀ n : ℕ, ∀ x : NumberField.RingOfIntegers L,
      (((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) - x ∈ P ^ n := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih x
  cases n with
  | zero =>
      simp
  | succ n =>
      cases n with
      | zero =>
          simpa using
            number_smul_sub
              (L := L) P (σ : P.inertia (Gal(L/ℚ))) x
      | succ n =>
          cases n with
          | zero =>
              exact
                (wild_inertia_subgroup
                  (L := L) P (σ : P.inertia (Gal(L/ℚ)))).1 σ.property x
          | succ n =>
              have hprev :
                  ∀ y : NumberField.RingOfIntegers L,
                    (((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • y) - y ∈
                      P ^ n.succ.succ := by
                exact ih n.succ.succ (by omega)
              exact hstep (n := n.succ.succ) (by omega) hprev x

lemma number_wild_powers
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q ℓ : ℕ} (hq : Nat.Prime q) (hℓ : Nat.Prime ℓ) (hℓ_ne_q : ℓ ≠ q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : number_wild_subgroup (L := L) P)
    (hσ_order : orderOf σ = ℓ) :
    ∀ n : ℕ, ∀ x : NumberField.RingOfIntegers L,
      (((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) - x ∈ P ^ n := by
  refine
    wild_all_powers
      (L := L) P σ ?_
  intro n hn hcong
  exact
    number_wild_congruence
      (L := L) hq hℓ hℓ_ne_q P σ hσ_order hn hcong

lemma wild_no_char
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q ℓ : ℕ} (hq : Nat.Prime q) (hℓ : Nat.Prime ℓ) (hℓ_ne_q : ℓ ≠ q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ¬ ∃ σ : number_wild_subgroup (L := L) P,
      σ ≠ 1 ∧ orderOf σ = ℓ := by
  rintro ⟨σ, hσ_ne_one, hσ_order⟩
  have h_all_powers :
      ∀ n : ℕ, ∀ x : NumberField.RingOfIntegers L,
        (((σ : P.inertia (Gal(L/ℚ))) : Gal(L/ℚ)) • x) - x ∈ P ^ n := by
    exact
      number_wild_powers
        (L := L) hq hℓ hℓ_ne_q P σ hσ_order
  have h_inertia_one :
      (σ : P.inertia (Gal(L/ℚ))) = 1 := by
    exact
      inertia_all_powers
        (L := L) hq P (σ : P.inertia (Gal(L/ℚ))) h_all_powers
  have h_wild_one : σ = 1 := by
    exact Subtype.ext h_inertia_one
  exact hσ_ne_one h_wild_one

lemma number_wild_group
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    IsPGroup q (number_wild_subgroup (L := L) P) := by
  classical
  refine p_no_ne
    (Γ := number_wild_subgroup (L := L) P) hq ?_
  intro ℓ hℓ hℓ_ne_q
  exact wild_no_char
    (L := L) hq hℓ hℓ_ne_q P

lemma number_stabilizer_smul
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : MulAction.stabilizer (Gal(L/ℚ)) P)
    {x : NumberField.RingOfIntegers L} (hx : x ∈ P) :
    ((σ : Gal(L/ℚ)) • x) ∈ P := by
  classical
  have hMem :
      ((σ : Gal(L/ℚ)) • x) ∈ (σ : Gal(L/ℚ)) • P :=
    Ideal.smul_mem_pointwise_smul (σ : Gal(L/ℚ)) x P hx
  rw [σ.property] at hMem
  exact hMem

lemma stabilizer_smul_sq
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : MulAction.stabilizer (Gal(L/ℚ)) P) :
    (σ : Gal(L/ℚ)) • (P ^ 2) = P ^ 2 := by
  calc
    (σ : Gal(L/ℚ)) • (P ^ 2) =
        ((σ : Gal(L/ℚ)) • P) ^ 2 := by
      simp [pow_two]
    _ = P ^ 2 := by
      rw [σ.property]

lemma number_stabilizer_sq
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : MulAction.stabilizer (Gal(L/ℚ)) P) :
    P ^ 2 =
      (P ^ 2).map
        ((MulSemiringAction.toRingEquiv (Gal(L/ℚ))
          (NumberField.RingOfIntegers L) (σ : Gal(L/ℚ))) :
            NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) := by
  have hPow :
      (σ : Gal(L/ℚ)) • (P ^ 2) = P ^ 2 :=
    stabilizer_smul_sq (L := L) P σ
  change P ^ 2 =
    (P ^ 2).map
      (MulSemiringAction.toRingHom (Gal(L/ℚ))
        (NumberField.RingOfIntegers L) (σ : Gal(L/ℚ)))
  rw [Ideal.map_pow]
  simpa [Ideal.pointwise_smul_def] using hPow.symm

noncomputable def number_stabilizer_square
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : MulAction.stabilizer (Gal(L/ℚ)) P) :
    (NumberField.RingOfIntegers L ⧸ P ^ 2) ≃+*
      (NumberField.RingOfIntegers L ⧸ P ^ 2) := by
  exact
    Ideal.quotientEquiv (P ^ 2) (P ^ 2)
      (MulSemiringAction.toRingEquiv (Gal(L/ℚ))
        (NumberField.RingOfIntegers L) (σ : Gal(L/ℚ)))
      (number_stabilizer_sq (L := L) P σ)

lemma stabilizer_square_mk
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : MulAction.stabilizer (Gal(L/ℚ)) P)
    (x : NumberField.RingOfIntegers L) :
    number_stabilizer_square (L := L) P σ
        (Ideal.Quotient.mk (P ^ 2) x) =
      Ideal.Quotient.mk (P ^ 2) ((σ : Gal(L/ℚ)) • x) := by
  exact
    Ideal.quotientEquiv_mk
      (I := P ^ 2) (J := P ^ 2)
      (f := MulSemiringAction.toRingEquiv (Gal(L/ℚ))
        (NumberField.RingOfIntegers L) (σ : Gal(L/ℚ)))
      (hIJ := number_stabilizer_sq (L := L) P σ) x

lemma stabilizer_square_cotangent
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : MulAction.stabilizer (Gal(L/ℚ)) P)
    {z : NumberField.RingOfIntegers L ⧸ P ^ 2}
    (hz : z ∈ P.cotangentIdeal) :
    number_stabilizer_square (L := L) P σ z ∈
      P.cotangentIdeal := by
  classical
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [stabilizer_square_mk]
  rw [Ideal.mk_mem_cotangentIdeal] at hz ⊢
  exact number_stabilizer_smul (L := L) P σ hz

noncomputable def number_stabilizer_ideal
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : MulAction.stabilizer (Gal(L/ℚ)) P) :
    P.cotangentIdeal → P.cotangentIdeal :=
  fun z =>
    ⟨number_stabilizer_square (L := L) P σ z,
      stabilizer_square_cotangent
        (L := L) P σ z.property⟩

lemma stabilizer_cotangent_mk
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : MulAction.stabilizer (Gal(L/ℚ)) P)
    (x : NumberField.RingOfIntegers L) (hx : x ∈ P) :
    number_stabilizer_ideal (L := L) P σ
        ⟨Ideal.Quotient.mk (P ^ 2) x, by
          rw [Ideal.mk_mem_cotangentIdeal]
          exact hx⟩ =
      ⟨Ideal.Quotient.mk (P ^ 2) ((σ : Gal(L/ℚ)) • x), by
        rw [Ideal.mk_mem_cotangentIdeal]
        exact number_stabilizer_smul (L := L) P σ hx⟩ := by
  ext
  exact stabilizer_square_mk (L := L) P σ x

lemma stabilizer_cotangent_mul
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ τ : MulAction.stabilizer (Gal(L/ℚ)) P) (z : P.cotangentIdeal) :
    number_stabilizer_ideal (L := L) P (σ * τ) z =
      number_stabilizer_ideal (L := L) P σ
        (number_stabilizer_ideal (L := L) P τ z) := by
  ext
  obtain ⟨x, hxz⟩ :=
    Ideal.Quotient.mk_surjective
      (z : NumberField.RingOfIntegers L ⧸ P ^ 2)
  change
    number_stabilizer_square (L := L) P (σ * τ)
        (z : NumberField.RingOfIntegers L ⧸ P ^ 2) =
      number_stabilizer_square (L := L) P σ
        (number_stabilizer_square (L := L) P τ z)
  rw [← hxz]
  rw [stabilizer_square_mk]
  rw [stabilizer_square_mk]
  rw [stabilizer_square_mk]
  have hmul :
      (((σ * τ : MulAction.stabilizer (Gal(L/ℚ)) P) : Gal(L/ℚ)) • x) =
        (σ : Gal(L/ℚ)) • ((τ : Gal(L/ℚ)) • x) := by
    simpa using (mul_smul (σ : Gal(L/ℚ)) (τ : Gal(L/ℚ)) x)
  exact congrArg (Ideal.Quotient.mk (P ^ 2)) hmul

lemma stabilizer_cotangent_ideal
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L)) (z : P.cotangentIdeal) :
    number_stabilizer_ideal (L := L) P 1 z = z := by
  ext
  obtain ⟨x, hxz⟩ :=
    Ideal.Quotient.mk_surjective
      (z : NumberField.RingOfIntegers L ⧸ P ^ 2)
  change
    number_stabilizer_square (L := L) P 1
        (z : NumberField.RingOfIntegers L ⧸ P ^ 2) =
      (z : NumberField.RingOfIntegers L ⧸ P ^ 2)
  rw [← hxz]
  rw [stabilizer_square_mk]
  simp

lemma stabilizer_cotangent_inv
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (σ : MulAction.stabilizer (Gal(L/ℚ)) P) (z : P.cotangentIdeal) :
    number_stabilizer_ideal (L := L) P σ
        (number_stabilizer_ideal (L := L) P σ⁻¹ z) = z := by
  calc
    number_stabilizer_ideal (L := L) P σ
        (number_stabilizer_ideal (L := L) P σ⁻¹ z) =
      number_stabilizer_ideal (L := L) P (σ * σ⁻¹) z := by
        exact
          (stabilizer_cotangent_mul
            (L := L) P σ σ⁻¹ z).symm
    _ = number_stabilizer_ideal (L := L) P 1 z := by
        rw [mul_inv_cancel]
    _ = z := by
        exact stabilizer_cotangent_ideal (L := L) P z

lemma number_cotangent_stabilizer
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (P : Ideal (NumberField.RingOfIntegers L))
    (τ : P.inertia (Gal(L/ℚ))) (z : P.cotangentIdeal) :
    field_cotangent_ideal (L := L) P τ z =
      number_stabilizer_ideal (L := L) P
        ⟨(τ : Gal(L/ℚ)), field_inertia_stabilizer (L := L) P τ⟩ z := by
  ext
  obtain ⟨x, hxz⟩ :=
    Ideal.Quotient.mk_surjective
      (z : NumberField.RingOfIntegers L ⧸ P ^ 2)
  change
    number_inertia_square (L := L) P τ
        (z : NumberField.RingOfIntegers L ⧸ P ^ 2) =
      number_stabilizer_square (L := L) P
        ⟨(τ : Gal(L/ℚ)), field_inertia_stabilizer (L := L) P τ⟩ z
  rw [← hxz]
  rw [number_square_mk]
  rw [stabilizer_square_mk]

noncomputable def number_field_stabilizer
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : MulAction.stabilizer (Gal(L/ℚ)) P) :
    letI : Module P.ResidueField P.cotangentIdeal :=
      number_residue_module (L := L) hq P
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    P.Cotangent → P.Cotangent := by
  classical
  letI : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  let e :=
    number_cotangent_residue (L := L) hq P
  exact fun y =>
    e (number_stabilizer_ideal (L := L) P σ (e.symm y))

lemma number_stabilizer_cotangent
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : MulAction.stabilizer (Gal(L/ℚ)) P) (z : P.cotangentIdeal) :
    letI : Module P.ResidueField P.cotangentIdeal :=
      number_residue_module (L := L) hq P
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    number_field_stabilizer (L := L) hq P σ
        (number_cotangent_residue (L := L) hq P z) =
      number_cotangent_residue (L := L) hq P
        (number_stabilizer_ideal (L := L) P σ z) := by
  classical
  letI : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  simp [number_field_stabilizer]

lemma field_stabilizer_cotangent
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : MulAction.stabilizer (Gal(L/ℚ)) P) (x : P) :
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    number_field_stabilizer (L := L) hq P σ (P.toCotangent x) =
      P.toCotangent
        ⟨(σ : Gal(L/ℚ)) • (x : NumberField.RingOfIntegers L),
          number_stabilizer_smul (L := L) P σ x.property⟩ := by
  classical
  letI : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  change
    P.cotangentEquivIdeal.symm
        (number_stabilizer_ideal (L := L) P σ
          (P.cotangentEquivIdeal (P.toCotangent x))) =
      P.toCotangent
        ⟨(σ : Gal(L/ℚ)) • (x : NumberField.RingOfIntegers L),
          number_stabilizer_smul (L := L) P σ x.property⟩
  have hsource :
      P.cotangentEquivIdeal (P.toCotangent x) =
        ⟨Ideal.Quotient.mk (P ^ 2) (x : NumberField.RingOfIntegers L), by
          rw [Ideal.mk_mem_cotangentIdeal]
          exact x.property⟩ := by
    ext
    simp
  rw [hsource]
  rw [stabilizer_cotangent_mk
    (L := L) P σ (x : NumberField.RingOfIntegers L) x.property]
  exact
    Ideal.cotangentEquivIdeal_symm_apply
      (I := P) ((σ : Gal(L/ℚ)) • (x : NumberField.RingOfIntegers L))
      (number_stabilizer_smul (L := L) P σ x.property)

lemma arith_frob_smul
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : Gal(L/ℚ)) (hσ : IsArithFrobAt ℤ σ P)
    (hσStab : σ ∈ MulAction.stabilizer (Gal(L/ℚ)) P)
    (a : P.ResidueField) (y : P.Cotangent) :
    letI : Module P.ResidueField P.Cotangent :=
      cotangent_residue_module (L := L) hq P
    number_field_stabilizer (L := L) hq P ⟨σ, hσStab⟩ (a • y) =
      a ^ q •
        number_field_stabilizer (L := L) hq P ⟨σ, hσStab⟩ y := by
  classical
  letI : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  obtain ⟨r, rfl⟩ :=
    number_residue_surjective (L := L) hq P a
  obtain ⟨x, hx⟩ := P.toCotangent_surjective y
  rw [← hx]
  rw [residue_smul_cotangent (L := L) hq P r x]
  rw [field_stabilizer_cotangent
    (L := L) hq P ⟨σ, hσStab⟩ (r • x)]
  rw [field_stabilizer_cotangent
    (L := L) hq P ⟨σ, hσStab⟩ x]
  rw [← number_arith_frob (L := L) P σ hσ r]
  rw [residue_smul_cotangent]
  apply (P.toCotangent_eq).mpr
  change σ • (r * (x : NumberField.RingOfIntegers L)) -
    (σ • r) * (σ • (x : NumberField.RingOfIntegers L)) ∈ P ^ 2
  rw [smul_mul']
  simp

def frobeniusSemilinearModule
    {K : Type*} {V : Type*} [Field K] [AddCommGroup V]
    (moduleInst : Module K V) (q : ℕ) (f : V → V) : Prop :=
  letI : Module K V := moduleInst
  ∀ a : K, ∀ z : V, f (a • z) = a ^ q • f z

lemma arith_frob_cotangent
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : Gal(L/ℚ)) (hσ : IsArithFrobAt ℤ σ P)
    (hσStab : σ ∈ MulAction.stabilizer (Gal(L/ℚ)) P) :
    frobeniusSemilinearModule
      (number_residue_module (L := L) hq P) q
      (number_stabilizer_ideal (L := L) P ⟨σ, hσStab⟩) := by
  classical
  let moduleInstIdeal : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  letI : Module P.ResidueField P.cotangentIdeal := moduleInstIdeal
  letI : SMul P.ResidueField P.cotangentIdeal := moduleInstIdeal.toSMul
  let moduleInstCotangent : Module P.ResidueField P.Cotangent :=
    cotangent_residue_module (L := L) hq P
  letI : Module P.ResidueField P.Cotangent := moduleInstCotangent
  letI : SMul P.ResidueField P.Cotangent := moduleInstCotangent.toSMul
  change ∀ a : P.ResidueField, ∀ z : P.cotangentIdeal,
    number_stabilizer_ideal (L := L) P ⟨σ, hσStab⟩ (a • z) =
      a ^ q • number_stabilizer_ideal (L := L) P ⟨σ, hσStab⟩ z
  intro a z
  let e : P.cotangentIdeal ≃ₗ[P.ResidueField] P.Cotangent :=
    number_cotangent_residue (L := L) hq P
  apply e.injective
  calc
    e (number_stabilizer_ideal (L := L) P ⟨σ, hσStab⟩ (a • z)) =
        number_field_stabilizer (L := L) hq P ⟨σ, hσStab⟩
          (e (a • z)) := by
            exact
              (number_stabilizer_cotangent
                (L := L) hq P ⟨σ, hσStab⟩ (a • z)).symm
    _ =
        number_field_stabilizer (L := L) hq P ⟨σ, hσStab⟩
          (a • e z) := by
            exact congrArg
              (number_field_stabilizer
                (L := L) hq P ⟨σ, hσStab⟩) (map_smul e a z)
    _ =
        a ^ q • number_field_stabilizer
          (L := L) hq P ⟨σ, hσStab⟩ (e z) := by
            exact
              arith_frob_smul
                (L := L) hq P σ hσ hσStab a (e z)
    _ =
        a ^ q • e
          (number_stabilizer_ideal (L := L) P ⟨σ, hσStab⟩ z) := by
            exact congrArg (fun y => a ^ q • y)
              (number_stabilizer_cotangent
                (L := L) hq P ⟨σ, hσStab⟩ z)
    _ =
        e (a ^ q •
          number_stabilizer_ideal (L := L) P ⟨σ, hσStab⟩ z) := by
            exact (map_smul e (a ^ q)
              (number_stabilizer_ideal (L := L) P ⟨σ, hσStab⟩ z)).symm

/--
The semilinear Frobenius-equivariance input for the tame local conjugation
relation: the error between Frobenius conjugation and the `q`-power map lies in
wild inertia.
-/
lemma arith_frob_wild
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : Gal(L/ℚ)) (hσ : IsArithFrobAt ℤ σ P)
    (τ : P.inertia (Gal(L/ℚ))) :
    ∃ ε : number_wild_subgroup (L := L) P,
      (ε : Gal(L/ℚ)) =
        σ * (τ : Gal(L/ℚ)) * σ⁻¹ *
          ((τ : Gal(L/ℚ)) ^ q)⁻¹ := by
  classical
  let moduleInstIdeal : Module P.ResidueField P.cotangentIdeal :=
    number_residue_module (L := L) hq P
  letI : Module P.ResidueField P.cotangentIdeal := moduleInstIdeal
  letI : SMul P.ResidueField P.cotangentIdeal := moduleInstIdeal.toSMul
  have hσInvStab : σ⁻¹ • P = P := by
    rw [Ideal.pointwise_smul_eq_comap]
    exact hσ.comap_eq
  have hσStab : σ ∈ MulAction.stabilizer (Gal(L/ℚ)) P := by
    have h := congrArg (fun Q : Ideal (NumberField.RingOfIntegers L) => σ • Q) hσInvStab
    simpa [smul_smul] using h.symm
  let σD : MulAction.stabilizer (Gal(L/ℚ)) P := ⟨σ, hσStab⟩
  let τD : MulAction.stabilizer (Gal(L/ℚ)) P :=
    ⟨(τ : Gal(L/ℚ)), field_inertia_stabilizer (L := L) P τ⟩
  have hconjMem :
      σ * (τ : Gal(L/ℚ)) * σ⁻¹ ∈ P.inertia (Gal(L/ℚ)) := by
    have hnormal :
        ((P.inertia (Gal(L/ℚ))).subgroupOf
          (MulAction.stabilizer (Gal(L/ℚ)) P)).Normal :=
      inferInstance
    have hmem :
        σD * τD * σD⁻¹ ∈
          (P.inertia (Gal(L/ℚ))).subgroupOf
            (MulAction.stabilizer (Gal(L/ℚ)) P) :=
      hnormal.conj_mem τD τ.property σD
    simpa [σD, τD] using hmem
  let conjI : P.inertia (Gal(L/ℚ)) :=
    ⟨σ * (τ : Gal(L/ℚ)) * σ⁻¹, hconjMem⟩
  let τPowI : P.inertia (Gal(L/ℚ)) := τ ^ q
  let εI : P.inertia (Gal(L/ℚ)) := conjI * τPowI⁻¹
  obtain ⟨v, hv_ne_zero, hv_span⟩ :=
    cotangent_residue_generator (L := L) hq P
  dsimp [dimensionalSpansElement] at hv_span
  obtain ⟨a, ha⟩ :=
    hv_span (field_cotangent_ideal (L := L) P τ v)
  obtain ⟨b, hb⟩ :=
    hv_span (number_stabilizer_ideal (L := L) P σD⁻¹ v)
  have hinertiaLinear
      (ι : P.inertia (Gal(L/ℚ))) (c : P.ResidueField) (z : P.cotangentIdeal) :
      field_cotangent_ideal (L := L) P ι (c • z) =
        c • field_cotangent_ideal (L := L) P ι z := by
    exact
      cotangent_representation_smul
        (L := L) hq P ι c z
  have hσSemilinear
      (c : P.ResidueField) (z : P.cotangentIdeal) :
      number_stabilizer_ideal (L := L) P σD (c • z) =
        c ^ q • number_stabilizer_ideal (L := L) P σD z := by
    have hsemi :=
      arith_frob_cotangent
        (L := L) hq P σ hσ hσStab
    dsimp [frobeniusSemilinearModule] at hsemi
    exact hsemi c z
  have hσb :
      b ^ q • number_stabilizer_ideal (L := L) P σD v = v := by
    calc
      b ^ q • number_stabilizer_ideal (L := L) P σD v =
          number_stabilizer_ideal (L := L) P σD (b • v) := by
            exact (hσSemilinear b v).symm
      _ =
          number_stabilizer_ideal (L := L) P σD
            (number_stabilizer_ideal (L := L) P σD⁻¹ v) := by
              rw [hb]
      _ = v := by
          exact stabilizer_cotangent_inv (L := L) P σD v
  have hconjD :
      number_stabilizer_ideal (L := L) P (σD * τD * σD⁻¹) v =
        a ^ q • v := by
    calc
      number_stabilizer_ideal (L := L) P (σD * τD * σD⁻¹) v =
          number_stabilizer_ideal (L := L) P σD
            (number_stabilizer_ideal (L := L) P τD
              (number_stabilizer_ideal (L := L) P σD⁻¹ v)) := by
                rw [stabilizer_cotangent_mul]
                rw [stabilizer_cotangent_mul]
      _ =
          number_stabilizer_ideal (L := L) P σD
            (number_stabilizer_ideal (L := L) P τD (b • v)) := by
              rw [hb]
      _ =
          number_stabilizer_ideal (L := L) P σD
            (field_cotangent_ideal (L := L) P τ (b • v)) := by
              rw [number_cotangent_stabilizer]
      _ =
          number_stabilizer_ideal (L := L) P σD
            (b • field_cotangent_ideal (L := L) P τ v) := by
              rw [hinertiaLinear]
      _ =
          number_stabilizer_ideal (L := L) P σD (b • (a • v)) := by
              rw [ha]
      _ =
          number_stabilizer_ideal (L := L) P σD ((b * a) • v) := by
              rw [mul_smul]
      _ =
          (b * a) ^ q • number_stabilizer_ideal (L := L) P σD v := by
              exact hσSemilinear (b * a) v
      _ =
          a ^ q •
            (b ^ q • number_stabilizer_ideal (L := L) P σD v) := by
              simp [mul_pow, mul_smul, mul_comm]
      _ = a ^ q • v := by
          rw [hσb]
  have hτPow (n : ℕ) :
      field_cotangent_ideal (L := L) P (τ ^ n) v =
        a ^ n • v := by
    induction n with
    | zero =>
        simp [number_cotangent_one]
    | succ n ih =>
        rw [show τ ^ (n + 1) = τ ^ n * τ by exact pow_succ τ n]
        rw [number_cotangent_mul]
        rw [← ha]
        rw [hinertiaLinear]
        rw [ih]
        simp [pow_succ, mul_smul, mul_comm]
  have hconjDEq :
      (⟨(conjI : Gal(L/ℚ)),
          field_inertia_stabilizer (L := L) P conjI⟩ :
        MulAction.stabilizer (Gal(L/ℚ)) P) =
        σD * τD * σD⁻¹ := by
    ext
    rfl
  have hconj :
      field_cotangent_ideal (L := L) P conjI v =
        a ^ q • v := by
    rw [number_cotangent_stabilizer]
    rw [hconjDEq]
    exact hconjD
  have hconjEqPow :
      ∀ z : P.cotangentIdeal,
        field_cotangent_ideal (L := L) P conjI z =
          field_cotangent_ideal (L := L) P τPowI z := by
    intro z
    obtain ⟨c, rfl⟩ := hv_span z
    rw [hinertiaLinear, hinertiaLinear]
    rw [hconj, show τPowI = τ ^ q by rfl, hτPow]
  have hεFixed :
      ∀ z : P.cotangentIdeal,
        field_cotangent_ideal (L := L) P εI z = z := by
    intro z
    rw [show εI = conjI * τPowI⁻¹ by rfl]
    rw [number_cotangent_mul]
    rw [hconjEqPow]
    exact inertia_cotangent_inv (L := L) P τPowI z
  have hεWild :
      εI ∈ number_wild_subgroup (L := L) P :=
    (inertia_cotangent_wild
      (L := L) hq P εI).1 hεFixed
  refine ⟨⟨εI, hεWild⟩, ?_⟩
  rfl

/--
At a tamely ramified rational prime, an arithmetic Frobenius conjugates every
inertia element by the cardinality of the base residue field.

For a prime above `q` in a number field, that cardinality is `q`.  This is the
ramified local conjugation theorem underlying the Koch tame relation.
-/
lemma arith_frob_inertia
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (hTame : RationalTamePrimes
      (S := NumberField.RingOfIntegers L) q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : Gal(L/ℚ)) (hσ : IsArithFrobAt ℤ σ P)
    (τ : P.inertia (Gal(L/ℚ))) :
    σ * (τ : Gal(L/ℚ)) * σ⁻¹ =
      (τ : Gal(L/ℚ)) ^ q := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  have hCardCoprime :
      Nat.Coprime q (Nat.card (P.inertia (Gal(L/ℚ)))) :=
    tame_inertia_coprime (L := L) hq hTame P
  have hWildPGroup :
      IsPGroup q (number_wild_subgroup (L := L) P) :=
    number_wild_group (L := L) hq P
  have hWildBot :
      number_wild_subgroup (L := L) P = ⊥ :=
    bot_coprime_card
      (number_wild_subgroup (L := L) P) hWildPGroup hCardCoprime
  obtain ⟨ε, hε⟩ :=
    arith_frob_wild
      (L := L) hq P σ hσ τ
  have hε_inertia_one :
      (ε : P.inertia (Gal(L/ℚ))) = 1 := by
    have hε_mem_bot :
        (ε : P.inertia (Gal(L/ℚ))) ∈
          (⊥ : Subgroup (P.inertia (Gal(L/ℚ)))) := by
      rw [← hWildBot]
      exact ε.property
    simpa using hε_mem_bot
  have hε_gal_one :
      (ε : Gal(L/ℚ)) = 1 := by
    exact congrArg (fun x : P.inertia (Gal(L/ℚ)) => (x : Gal(L/ℚ)))
      hε_inertia_one
  apply eq_of_mul_inv_eq_one
  rw [← hε, hε_gal_one]

lemma tame_inertia_arithmetic
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∃ χ : P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ,
      IsPGroup q χ.ker := by
  classical
  obtain ⟨χ, hχKer⟩ :=
    tame_uniformizer_wild
      (L := L) hq P
  refine ⟨χ, ?_⟩
  have hWild :
      IsPGroup q (number_wild_subgroup (L := L) P) := by
    exact number_wild_group (L := L) hq P
  rw [hχKer]
  exact hWild

lemma tame_inertia_sylow
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (_hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (hχ :
      ∃ χ : P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ,
        IsPGroup q χ.ker) :
    ∃ (S : Sylow q (P.inertia (Gal(L/ℚ))))
      (χ : P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ),
        χ.ker ≤ (S : Subgroup (P.inertia (Gal(L/ℚ)))) := by
  classical
  obtain ⟨χ, hKerP⟩ := hχ
  obtain ⟨S, hKerS⟩ :=
    monoid_sylow_p χ hKerP
  exact ⟨S, χ, hKerS⟩

lemma tame_character_sylow
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∃ (S : Sylow q (P.inertia (Gal(L/ℚ))))
      (χ : P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ),
        χ.ker ≤ (S : Subgroup (P.inertia (Gal(L/ℚ)))) := by
  classical
  have hχ :
      ∃ χ : P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ,
        IsPGroup q χ.ker := by
    exact
      tame_inertia_arithmetic
        (L := L) hq P
  exact
    tame_inertia_sylow
      (L := L) hq P hχ

lemma tame_inertia_character
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∃ χ : P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ,
      IsPGroup q χ.ker := by
  classical
  exact
    tame_inertia_arithmetic
      (L := L) hq P

lemma tame_inertia_embedding
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (hCardCoprime : Nat.Coprime q (Nat.card (P.inertia (Gal(L/ℚ))))) :
    ∃ χ : P.inertia (Gal(L/ℚ)) →* P.ResidueFieldˣ,
      Function.Injective χ := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  obtain ⟨χ, hχKer⟩ :=
    tame_inertia_character
      (L := L) hq P
  refine ⟨χ, ?_⟩
  exact
    monoid_coprime_card
      χ hχKer hCardCoprime

lemma tame_inertia_units
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∃ χ : P.inertia (Gal(L/ℚ)) →*
        (NumberField.RingOfIntegers L ⧸ P)ˣ,
      IsPGroup q χ.ker := by
  classical
  letI : P.IsMaximal :=
    number_above_maximal (L := L) hq P
  obtain ⟨χlocal, hχlocal⟩ :=
    tame_inertia_character
      (L := L) hq P
  let eUnits :
      (NumberField.RingOfIntegers L ⧸ P)ˣ ≃* P.ResidueFieldˣ :=
    unitsResidueMaximal P
  let χ : P.inertia (Gal(L/ℚ)) →*
      (NumberField.RingOfIntegers L ⧸ P)ˣ :=
    eUnits.symm.toMonoidHom.comp χlocal
  refine ⟨χ, ?_⟩
  exact p_ker_comp eUnits.symm χlocal hχlocal

lemma tame_units_embedding
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (hCardCoprime : Nat.Coprime q (Nat.card (P.inertia (Gal(L/ℚ))))) :
    ∃ χ : P.inertia (Gal(L/ℚ)) →*
        (NumberField.RingOfIntegers L ⧸ P)ˣ,
      Function.Injective χ := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  obtain ⟨χ, hχKer⟩ :=
    tame_inertia_units
      (L := L) hq P
  refine ⟨χ, ?_⟩
  exact
    monoid_coprime_card
      χ hχKer hCardCoprime

lemma tame_cyclic
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (hTame : RationalTamePrimes
      (S := NumberField.RingOfIntegers L) q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    IsCyclic (P.inertia (Gal(L/ℚ))) := by
  classical
  have hCardCoprime :
      Nat.Coprime q (Nat.card (P.inertia (Gal(L/ℚ)))) :=
    tame_inertia_coprime (L := L) hq hTame P
  obtain ⟨χ, hχ⟩ :=
    tame_units_embedding
      (L := L) hq P hCardCoprime
  exact
    cyclic_injective_units
      (L := L) hq P χ hχ

lemma decomposition_inertia_cyclic
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    IsCyclic
      (MulAction.stabilizer (Gal(L/ℚ)) P ⧸
        (P.inertia (Gal(L/ℚ))).subgroupOf
          (MulAction.stabilizer (Gal(L/ℚ)) P)) := by
  classical
  let p : Ideal ℤ := Ideal.rationalPrimeIdeal q
  letI : p.IsPrime := rational_prime_ideal hq
  letI : P.LiesOver p := by
    simpa [p] using (inferInstance : P.LiesOver (Ideal.rationalPrimeIdeal q))
  have hp_ne_bot : p ≠ ⊥ := by
    dsimp [p, Ideal.rationalPrimeIdeal]
    exact mt Ideal.span_singleton_eq_bot.mp (by exact_mod_cast hq.ne_zero)
  letI : p.IsMaximal := Ring.HasFiniteQuotients.maximalOfPrime hp_ne_bot
  have hP_ne_bot : P ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hp_ne_bot P
  letI : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP_ne_bot inferInstance
  letI : Field (ℤ ⧸ p) := Ideal.Quotient.field p
  letI : Field (NumberField.RingOfIntegers L ⧸ P) := Ideal.Quotient.field P
  have hResidueFinite : Finite (NumberField.RingOfIntegers L ⧸ P) := inferInstance
  letI : Finite (NumberField.RingOfIntegers L ⧸ P) := hResidueFinite
  letI : Finite (Gal(L/ℚ)) :=
    IsGaloisGroup.finite (Gal(L/ℚ)) ℚ L
  letI : IsGaloisGroup (Gal(L/ℚ)) ℤ (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing
      (Gal(L/ℚ)) ℤ (NumberField.RingOfIntegers L) ℚ L
  letI : Algebra.IsInvariant ℤ (NumberField.RingOfIntegers L) (Gal(L/ℚ)) :=
    inferInstance
  let e :
      MulAction.stabilizer (Gal(L/ℚ)) P ⧸
          (P.inertia (Gal(L/ℚ))).subgroupOf
            (MulAction.stabilizer (Gal(L/ℚ)) P) ≃*
        Gal((NumberField.RingOfIntegers L ⧸ P)/(ℤ ⧸ p)) :=
    Ideal.Quotient.stabilizerQuotientInertiaEquiv (Gal(L/ℚ)) p P
  have hResidue :
      IsCyclic (Gal((NumberField.RingOfIntegers L ⧸ P)/(ℤ ⧸ p))) :=
    galois_group_cyclic
      (k := ℤ ⧸ p) (K := NumberField.RingOfIntegers L ⧸ P)
  exact e.isCyclic.mpr hResidue

lemma tame_decomposition_metacyclic
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (hTame : RationalTamePrimes
      (S := NumberField.RingOfIntegers L) q)
    (P : Ideal (NumberField.RingOfIntegers L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    IMSubgro (MulAction.stabilizer (Gal(L/ℚ)) P) := by
  classical
  let D : Subgroup (Gal(L/ℚ)) := MulAction.stabilizer (Gal(L/ℚ)) P
  let I : Subgroup D :=
    (P.inertia (Gal(L/ℚ))).subgroupOf D
  have hI_normal : I.Normal := by
    change
      ((P.inertia (Gal(L/ℚ))).subgroupOf
        (MulAction.stabilizer (Gal(L/ℚ)) P)).Normal
    infer_instance
  have hI_cyclic_as_subgroup :
      IsCyclic (P.inertia (Gal(L/ℚ))) :=
    tame_cyclic (L := L) hq hTame P
  have hI_cyclic : IsCyclic I := by
    let eI : I ≃* P.inertia (Gal(L/ℚ)) :=
      Subgroup.subgroupOfEquivOfLe (Ideal.inertia_le_stabilizer P)
    exact eI.isCyclic.mpr hI_cyclic_as_subgroup
  have hquot_cyclic :
      IsCyclic (D ⧸ I) := by
    simpa [D, I] using
      decomposition_inertia_cyclic (L := L) hq P
  exact ⟨I, hI_normal, hI_cyclic, hquot_cyclic⟩

end Towers
