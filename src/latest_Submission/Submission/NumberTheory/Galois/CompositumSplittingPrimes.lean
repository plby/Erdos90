import Submission.NumberTheory.Density.SplittingPrimeDensity
import Submission.NumberTheory.Galois.FrobeniusElement
import Submission.NumberTheory.Galois.DecompositionGroup

/-!
# Completely split primes in a compositum

A prime splits completely in the compositum of two finite Galois extensions
exactly when it splits completely in both extensions.  The proof uses
restriction of decomposition groups and the ramification/inertia tower
formulas.
-/

namespace Submission.NumberTheory.Milne

open IsDedekindDomain NumberField
open scoped NumberField Pointwise

noncomputable section

variable {K Omega : Type*} [Field K] [NumberField K]
  [Field Omega] [NumberField Omega] [Algebra K Omega]

noncomputable local instance ringOfIntegersGalAction
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] :
    MulSemiringAction Gal(E/F) (NumberField.RingOfIntegers E) :=
  IsIntegralClosure.MulSemiringAction
    (NumberField.RingOfIntegers F) F E (NumberField.RingOfIntegers E)

lemma integers_smul_restrict
    {F E N : Type*} [Field F] [NumberField F]
    [Field E] [NumberField E] [Field N] [NumberField N]
    [Algebra F E] [Algebra F N] [Algebra E N] [IsScalarTower F E N]
    [IsGalois F E] [IsGalois F N]
    (sigma : Gal(N/F)) (x : NumberField.RingOfIntegers E) :
    sigma • algebraMap (NumberField.RingOfIntegers E)
        (NumberField.RingOfIntegers N) x =
      algebraMap (NumberField.RingOfIntegers E)
        (NumberField.RingOfIntegers N)
        ((AlgEquiv.restrictNormalHom E sigma) • x) := by
  apply Subtype.ext
  let y : NumberField.RingOfIntegers N :=
    algebraMap (NumberField.RingOfIntegers E)
      (NumberField.RingOfIntegers N) x
  calc
    algebraMap (NumberField.RingOfIntegers N) N
        (sigma • algebraMap (NumberField.RingOfIntegers E)
          (NumberField.RingOfIntegers N) x) =
        sigma (algebraMap (NumberField.RingOfIntegers N) N y) := by
      exact algebraMap_galRestrict_apply
        (A := NumberField.RingOfIntegers F) (K := F) (L := N)
        (B := NumberField.RingOfIntegers N) sigma y
    _ = sigma (algebraMap E N
        (algebraMap (NumberField.RingOfIntegers E) E x)) := by rfl
    _ = algebraMap E N
        ((AlgEquiv.restrictNormalHom E sigma)
          (algebraMap (NumberField.RingOfIntegers E) E x)) := by
      change sigma (algebraMap E N
          (algebraMap (NumberField.RingOfIntegers E) E x)) =
        algebraMap E N
          (sigma.restrictNormal E
            (algebraMap (NumberField.RingOfIntegers E) E x))
      exact (AlgEquiv.restrictNormal_commutes sigma E
        (algebraMap (NumberField.RingOfIntegers E) E x)).symm
    _ = algebraMap E N
        (algebraMap (NumberField.RingOfIntegers E) E
          ((AlgEquiv.restrictNormalHom E sigma) • x)) := by
      congr 1
      exact (algebraMap_galRestrict_apply
        (A := NumberField.RingOfIntegers F) (K := F) (L := E)
        (B := NumberField.RingOfIntegers E)
        (AlgEquiv.restrictNormalHom E sigma) x).symm
    _ = algebraMap (NumberField.RingOfIntegers N) N
        (algebraMap (NumberField.RingOfIntegers E)
          (NumberField.RingOfIntegers N)
          ((AlgEquiv.restrictNormalHom E sigma) • x)) := by rfl

lemma smul_restrict
    {F E N : Type*} [Field F] [NumberField F]
    [Field E] [NumberField E] [Field N] [NumberField N]
    [Algebra F E] [Algebra F N] [Algebra E N] [IsScalarTower F E N]
    [IsGalois F E] [IsGalois F N]
    (sigma : Gal(N/F)) (P : Ideal (NumberField.RingOfIntegers N)) :
    Ideal.under (NumberField.RingOfIntegers E) (sigma • P) =
      (AlgEquiv.restrictNormalHom E sigma) •
        Ideal.under (NumberField.RingOfIntegers E) P := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_comap]
  change
    (sigma⁻¹ • algebraMap (NumberField.RingOfIntegers E)
        (NumberField.RingOfIntegers N) x) ∈ P ↔
      algebraMap (NumberField.RingOfIntegers E)
        (NumberField.RingOfIntegers N)
        ((AlgEquiv.restrictNormalHom E sigma)⁻¹ • x) ∈ P
  have h := integers_smul_restrict
    (F := F) (E := E) (N := N) (sigma := sigma⁻¹) (x := x)
  constructor <;> intro hx
  · have hx' :
        algebraMap (NumberField.RingOfIntegers E)
          (NumberField.RingOfIntegers N)
          (AlgEquiv.restrictNormalHom E sigma⁻¹ • x) ∈ P := h ▸ hx
    simpa using hx'
  · have hx' :
        algebraMap (NumberField.RingOfIntegers E)
          (NumberField.RingOfIntegers N)
          (AlgEquiv.restrictNormalHom E sigma⁻¹ • x) ∈ P := by
      simpa using hx
    exact h.symm ▸ hx'

theorem splits_completely_bot
    {L : Type*} [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L]
    (p : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (P : Ideal (NumberField.RingOfIntegers L))
    (hP : P ∈ Ideal.primesOver p.asIdeal (NumberField.RingOfIntegers L)) :
    SplitsCompletelyAt K L p ↔
      MulAction.stabilizer Gal(L/K) P = ⊥ := by
  letI : IsGaloisGroup Gal(L/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) K L
  letI : P.IsPrime := hP.1
  letI : P.LiesOver p.asIdeal := hP.2
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver p.ne_bot hP
  letI : P.IsMaximal := Ideal.IsPrime.isMaximal (show P.IsPrime from inferInstance) hP0
  letI : Field (NumberField.RingOfIntegers K ⧸ p.asIdeal) :=
    Ideal.Quotient.field p.asIdeal
  letI : Field (NumberField.RingOfIntegers L ⧸ P) := Ideal.Quotient.field P
  letI : Finite (NumberField.RingOfIntegers K ⧸ p.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient p.ne_bot
  letI : Finite (NumberField.RingOfIntegers L ⧸ P) :=
    Ring.HasFiniteQuotients.finiteQuotient hP0
  constructor
  · intro hsplit
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro sigma hsigma
    have hcard := decomposition_inertia_deg
      (G := Gal(L/K)) p.asIdeal p.ne_bot P
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx
        (p := p.asIdeal) (P := P) (B := NumberField.RingOfIntegers L)
        (G := Gal(L/K)),
      Ideal.inertiaDegIn_eq_inertiaDeg
        (p := p.asIdeal) (P := P) (B := NumberField.RingOfIntegers L)
        (G := Gal(L/K)),
      (hsplit.2 P hP).1, (hsplit.2 P hP).2, mul_one] at hcard
    haveI : Subsingleton (MulAction.stabilizer Gal(L/K) P) :=
      (Nat.card_eq_one_iff_unique.mp hcard).1
    exact congrArg Subtype.val
      (Subsingleton.elim
        (⟨sigma, hsigma⟩ : MulAction.stabilizer Gal(L/K) P) 1)
  · intro hstab
    have hcard := decomposition_inertia_deg
      (G := Gal(L/K)) p.asIdeal p.ne_bot P
    rw [hstab, Nat.card_eq_fintype_card, Fintype.card_unique] at hcard
    have heIn : Ideal.ramificationIdxIn p.asIdeal
        (NumberField.RingOfIntegers L) = 1 :=
      Nat.eq_one_of_mul_eq_one_right hcard.symm
    have hfIn : Ideal.inertiaDegIn p.asIdeal
        (NumberField.RingOfIntegers L) = 1 :=
      Nat.eq_one_of_mul_eq_one_left hcard.symm
    apply splits_completely_prime K L p P hP
    · rwa [Ideal.ramificationIdxIn_eq_ramificationIdx
        (p := p.asIdeal) (P := P) (B := NumberField.RingOfIntegers L)
        (G := Gal(L/K))] at heIn
    · rwa [Ideal.inertiaDegIn_eq_inertiaDeg
        (p := p.asIdeal) (P := P) (B := NumberField.RingOfIntegers L)
        (G := Gal(L/K))] at hfIn

theorem splits_completely_tower
    {E N : Type*} [Field E] [NumberField E]
    [Field N] [NumberField N]
    [Algebra K E] [Algebra K N] [Algebra E N] [IsScalarTower K E N]
    [IsGalois K E] [IsGalois K N] [IsGalois E N]
    (p : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hsplit : SplitsCompletelyAt K N p) :
    SplitsCompletelyAt K E p := by
  letI : IsScalarTower (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers N) := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply K E N x
  letI : IsGaloisGroup Gal(E/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers E) :=
    IsGaloisGroup.of_isFractionRing Gal(E/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers E) K E
  letI : IsGaloisGroup Gal(N/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers N) :=
    IsGaloisGroup.of_isFractionRing Gal(N/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers N) K N
  letI : IsGaloisGroup Gal(N/E) (NumberField.RingOfIntegers E)
      (NumberField.RingOfIntegers N) :=
    IsGaloisGroup.of_isFractionRing Gal(N/E) (NumberField.RingOfIntegers E)
      (NumberField.RingOfIntegers N) E N
  obtain ⟨⟨P, hPprime, hPover⟩⟩ :=
    p.asIdeal.nonempty_primesOver (S := NumberField.RingOfIntegers N)
  letI : P.IsPrime := hPprime
  letI : P.LiesOver p.asIdeal := hPover
  let Q : Ideal (NumberField.RingOfIntegers E) :=
    P.under (NumberField.RingOfIntegers E)
  letI : Q.IsPrime := Ideal.IsPrime.under (NumberField.RingOfIntegers E) P
  letI : P.LiesOver Q := ⟨rfl⟩
  letI : Q.LiesOver p.asIdeal := ⟨by
    dsimp [Q]
    rw [Ideal.under_under]
    exact hPover.over⟩
  have hQ0 : Q ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot Q
  letI : Q.IsMaximal := Ideal.IsPrime.isMaximal
    (show Q.IsPrime from inferInstance) hQ0
  have hPmem : P ∈ Ideal.primesOver p.asIdeal
      (NumberField.RingOfIntegers N) := ⟨hPprime, hPover⟩
  have hQmem : Q ∈ Ideal.primesOver p.asIdeal
      (NumberField.RingOfIntegers E) := ⟨inferInstance, inferInstance⟩
  have heNIn : p.asIdeal.ramificationIdxIn
      (NumberField.RingOfIntegers N) = 1 := by
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx
      (p := p.asIdeal) (P := P) (B := NumberField.RingOfIntegers N)
      (G := Gal(N/K))]
    exact (hsplit.2 P hPmem).1
  have hfNIn : p.asIdeal.inertiaDegIn
      (NumberField.RingOfIntegers N) = 1 := by
    rw [Ideal.inertiaDegIn_eq_inertiaDeg
      (p := p.asIdeal) (P := P) (B := NumberField.RingOfIntegers N)
      (G := Gal(N/K))]
    exact (hsplit.2 P hPmem).2
  have heEIn : p.asIdeal.ramificationIdxIn
      (NumberField.RingOfIntegers E) = 1 := by
    have hmul := Ideal.ramificationIdxIn_mul_ramificationIdxIn'
      (p := p.asIdeal) Q (Gal(E/K)) (NumberField.RingOfIntegers N)
      (Gal(N/K)) (Gal(N/E))
    rw [heNIn] at hmul
    exact Nat.eq_one_of_mul_eq_one_right hmul
  have hfEIn : p.asIdeal.inertiaDegIn
      (NumberField.RingOfIntegers E) = 1 := by
    have hmul := Ideal.inertiaDegIn_mul_inertiaDegIn
      (p := p.asIdeal) Q (Gal(E/K)) (NumberField.RingOfIntegers N)
      (Gal(N/K)) (Gal(N/E))
    rw [hfNIn] at hmul
    exact Nat.eq_one_of_mul_eq_one_right hmul
  apply splits_completely_prime K E p Q hQmem
  · rwa [Ideal.ramificationIdxIn_eq_ramificationIdx
      (p := p.asIdeal) (P := Q) (B := NumberField.RingOfIntegers E)
      (G := Gal(E/K))] at heEIn
  · rwa [Ideal.inertiaDegIn_eq_inertiaDeg
      (p := p.asIdeal) (P := Q) (B := NumberField.RingOfIntegers E)
      (G := Gal(E/K))] at hfEIn

theorem splitting_inter_top
    {N : Type*} [Field N] [NumberField N] [Algebra K N] [IsGalois K N]
    (L M : IntermediateField K N) [IsGalois K L] [IsGalois K M]
    (hsup : L ⊔ M = ⊤) :
    splittingPrimes K N = splittingPrimes K L ∩ splittingPrimes K M := by
  ext p
  simp only [splitting_primes, Set.mem_inter_iff]
  constructor
  · intro hsplit
    exact ⟨splits_completely_tower (E := L) p hsplit,
      splits_completely_tower (E := M) p hsplit⟩
  · rintro ⟨hsplitL, hsplitM⟩
    obtain ⟨⟨P, hPprime, hPover⟩⟩ :=
      p.asIdeal.nonempty_primesOver (S := NumberField.RingOfIntegers N)
    letI : P.IsPrime := hPprime
    letI : P.LiesOver p.asIdeal := hPover
    have hPmem : P ∈ Ideal.primesOver p.asIdeal
        (NumberField.RingOfIntegers N) := ⟨hPprime, hPover⟩
    let QL : Ideal (NumberField.RingOfIntegers L) :=
      P.under (NumberField.RingOfIntegers L)
    let QM : Ideal (NumberField.RingOfIntegers M) :=
      P.under (NumberField.RingOfIntegers M)
    letI : QL.IsPrime := Ideal.IsPrime.under (NumberField.RingOfIntegers L) P
    letI : QM.IsPrime := Ideal.IsPrime.under (NumberField.RingOfIntegers M) P
    letI : QL.LiesOver p.asIdeal := ⟨by
      dsimp [QL]
      rw [Ideal.under_under]
      exact hPover.over⟩
    letI : QM.LiesOver p.asIdeal := ⟨by
      dsimp [QM]
      rw [Ideal.under_under]
      exact hPover.over⟩
    have hQLmem : QL ∈ Ideal.primesOver p.asIdeal
        (NumberField.RingOfIntegers L) := ⟨inferInstance, inferInstance⟩
    have hQMmem : QM ∈ Ideal.primesOver p.asIdeal
        (NumberField.RingOfIntegers M) := ⟨inferInstance, inferInstance⟩
    let resL : Gal(N/K) →* Gal(L/K) := AlgEquiv.restrictNormalHom L
    let resM : Gal(N/K) →* Gal(M/K) := AlgEquiv.restrictNormalHom M
    have hstabL : MulAction.stabilizer Gal(L/K) QL = ⊥ :=
      (splits_completely_bot p QL hQLmem).mp hsplitL
    have hstabM : MulAction.stabilizer Gal(M/K) QM = ⊥ :=
      (splits_completely_bot p QM hQMmem).mp hsplitM
    apply (splits_completely_bot p P hPmem).mpr
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro sigma hsigma
    have hsigmaP : sigma • P = P := MulAction.mem_stabilizer_iff.mp hsigma
    have hresLmem : resL sigma ∈ MulAction.stabilizer Gal(L/K) QL := by
      apply MulAction.mem_stabilizer_iff.mpr
      calc
        resL sigma • QL =
            Ideal.under (NumberField.RingOfIntegers L) (sigma • P) := by
          exact (smul_restrict
            (F := K) (E := L) (N := N) sigma P).symm
        _ = QL := by rw [hsigmaP]
    have hresMmem : resM sigma ∈ MulAction.stabilizer Gal(M/K) QM := by
      apply MulAction.mem_stabilizer_iff.mpr
      calc
        resM sigma • QM =
            Ideal.under (NumberField.RingOfIntegers M) (sigma • P) := by
          exact (smul_restrict
            (F := K) (E := M) (N := N) sigma P).symm
        _ = QM := by rw [hsigmaP]
    have hresL : resL sigma = 1 := by
      rw [hstabL] at hresLmem
      exact hresLmem
    have hresM : resM sigma = 1 := by
      rw [hstabM] at hresMmem
      exact hresMmem
    have hinjective : Function.Injective (resL.prod resM) := by
      rw [injective_iff_map_eq_one]
      intro tau htau
      have htau' : resL tau = 1 ∧ resM tau = 1 := Prod.mk_eq_one.mp htau
      have hfixL : tau ∈ L.fixingSubgroup := by
        rw [← L.restrictNormalHom_ker]
        exact htau'.1
      have hfixM : tau ∈ M.fixingSubgroup := by
        rw [← M.restrictNormalHom_ker]
        exact htau'.2
      have hfixsup : tau ∈ (L ⊔ M).fixingSubgroup := by
        rw [IntermediateField.fixingSubgroup_sup]
        exact ⟨hfixL, hfixM⟩
      rw [hsup, IntermediateField.fixingSubgroup_top] at hfixsup
      exact hfixsup
    apply hinjective
    rw [map_one]
    exact Prod.ext hresL hresM

set_option maxHeartbeats 800000 in
-- Restricted intermediate fields make this wrapper expensive to elaborate.
theorem splitting_sup_inter (L M : IntermediateField K Omega)
    [IsGalois K L] [IsGalois K M] :
    splittingPrimes K (L ⊔ M : IntermediateField K Omega) =
      splittingPrimes K L ∩ splittingPrimes K M := by
  let C : IntermediateField K Omega := L ⊔ M
  have hLC : L ≤ C := le_sup_left
  have hMC : M ≤ C := le_sup_right
  letI : Algebra L C := RingHom.toAlgebra (IntermediateField.inclusion hLC)
  letI : Algebra M C := RingHom.toAlgebra (IntermediateField.inclusion hMC)
  letI : IsScalarTower K L C := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    apply Subtype.ext
    rfl
  letI : IsScalarTower K M C := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    apply Subtype.ext
    rfl
  letI : IsGalois K C := inferInstance
  letI : IsGalois L C := IsGalois.tower_top_of_isGalois K L C
  letI : IsGalois M C := IsGalois.tower_top_of_isGalois K M C
  ext p
  simp only [splitting_primes, Set.mem_inter_iff]
  constructor
  · intro hsplit
    exact ⟨splits_completely_tower (E := L) p hsplit,
      splits_completely_tower (E := M) p hsplit⟩
  · rintro ⟨hsplitL, hsplitM⟩
    obtain ⟨⟨P, hPprime, hPover⟩⟩ :=
      p.asIdeal.nonempty_primesOver (S := NumberField.RingOfIntegers C)
    letI : P.IsPrime := hPprime
    letI : P.LiesOver p.asIdeal := hPover
    have hPmem : P ∈ Ideal.primesOver p.asIdeal
        (NumberField.RingOfIntegers C) := ⟨hPprime, hPover⟩
    let QL : Ideal (NumberField.RingOfIntegers L) :=
      P.under (NumberField.RingOfIntegers L)
    let QM : Ideal (NumberField.RingOfIntegers M) :=
      P.under (NumberField.RingOfIntegers M)
    letI : QL.IsPrime := Ideal.IsPrime.under (NumberField.RingOfIntegers L) P
    letI : QM.IsPrime := Ideal.IsPrime.under (NumberField.RingOfIntegers M) P
    letI : QL.LiesOver p.asIdeal := ⟨by
      dsimp [QL]
      rw [Ideal.under_under]
      exact hPover.over⟩
    letI : QM.LiesOver p.asIdeal := ⟨by
      dsimp [QM]
      rw [Ideal.under_under]
      exact hPover.over⟩
    have hQLmem : QL ∈ Ideal.primesOver p.asIdeal
        (NumberField.RingOfIntegers L) := ⟨inferInstance, inferInstance⟩
    have hQMmem : QM ∈ Ideal.primesOver p.asIdeal
        (NumberField.RingOfIntegers M) := ⟨inferInstance, inferInstance⟩
    let resL : Gal(C/K) →* Gal(L/K) := AlgEquiv.restrictNormalHom L
    let resM : Gal(C/K) →* Gal(M/K) := AlgEquiv.restrictNormalHom M
    have hstabL : MulAction.stabilizer Gal(L/K) QL = ⊥ :=
      (splits_completely_bot p QL hQLmem).mp hsplitL
    have hstabM : MulAction.stabilizer Gal(M/K) QM = ⊥ :=
      (splits_completely_bot p QM hQMmem).mp hsplitM
    apply (splits_completely_bot p P hPmem).mpr
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro sigma hsigma
    have hsigmaP : sigma • P = P := MulAction.mem_stabilizer_iff.mp hsigma
    have hresLmem : resL sigma ∈ MulAction.stabilizer Gal(L/K) QL := by
      apply MulAction.mem_stabilizer_iff.mpr
      calc
        resL sigma • QL =
            Ideal.under (NumberField.RingOfIntegers L) (sigma • P) := by
          exact (smul_restrict
            (F := K) (E := L) (N := C) sigma P).symm
        _ = QL := by rw [hsigmaP]
    have hresMmem : resM sigma ∈ MulAction.stabilizer Gal(M/K) QM := by
      apply MulAction.mem_stabilizer_iff.mpr
      calc
        resM sigma • QM =
            Ideal.under (NumberField.RingOfIntegers M) (sigma • P) := by
          exact (smul_restrict
            (F := K) (E := M) (N := C) sigma P).symm
        _ = QM := by rw [hsigmaP]
    have hresL : resL sigma = 1 := by
      rw [hstabL] at hresLmem
      exact hresLmem
    have hresM : resM sigma = 1 := by
      rw [hstabM] at hresMmem
      exact hresMmem
    have hinjective : Function.Injective (resL.prod resM) := by
      let LC : IntermediateField K C := IntermediateField.restrict hLC
      let MC : IntermediateField K C := IntermediateField.restrict hMC
      have hsupC : LC ⊔ MC = ⊤ := by
        apply (IntermediateField.lift_injective C)
        rw [IntermediateField.lift_sup, IntermediateField.lift_top]
        rw [show IntermediateField.lift LC = L from
            IntermediateField.lift_restrict hLC,
          show IntermediateField.lift MC = M from
            IntermediateField.lift_restrict hMC]
      rw [injective_iff_map_eq_one]
      intro tau htau
      have htau' : resL tau = 1 ∧ resM tau = 1 := Prod.mk_eq_one.mp htau
      have hfixL : tau ∈ LC.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        have hxL : x.1 ∈ L :=
          (IntermediateField.mem_restrict hLC x).mp hx
        let y : L := ⟨x.1, hxL⟩
        have hcomm := AlgEquiv.restrictNormal_commutes tau L y
        have htauL : AlgEquiv.restrictNormalHom L tau = 1 := htau'.1
        change algebraMap L C ((AlgEquiv.restrictNormalHom L tau) y) =
          tau (algebraMap L C y) at hcomm
        rw [htauL] at hcomm
        have hyx : algebraMap L C y = x := by
          apply Subtype.ext
          rfl
        rw [hyx] at hcomm
        exact hcomm.symm
      have hfixM : tau ∈ MC.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        have hxM : x.1 ∈ M :=
          (IntermediateField.mem_restrict hMC x).mp hx
        let y : M := ⟨x.1, hxM⟩
        have hcomm := AlgEquiv.restrictNormal_commutes tau M y
        have htauM : AlgEquiv.restrictNormalHom M tau = 1 := htau'.2
        change algebraMap M C ((AlgEquiv.restrictNormalHom M tau) y) =
          tau (algebraMap M C y) at hcomm
        rw [htauM] at hcomm
        have hyx : algebraMap M C y = x := by
          apply Subtype.ext
          rfl
        rw [hyx] at hcomm
        exact hcomm.symm
      have hfixsup : tau ∈ (LC ⊔ MC).fixingSubgroup := by
        rw [IntermediateField.fixingSubgroup_sup]
        exact ⟨hfixL, hfixM⟩
      rw [hsupC, IntermediateField.fixingSubgroup_top] at hfixsup
      exact hfixsup
    apply hinjective
    change (resL sigma, resM sigma) = (resL 1, resM 1)
    simp only [map_one, hresL, hresM]

end

end Submission.NumberTheory.Milne
