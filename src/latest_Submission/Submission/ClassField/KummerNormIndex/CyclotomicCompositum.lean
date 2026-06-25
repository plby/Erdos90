import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.NumberTheory.Cyclotomic.Gal
import Submission.ClassField.KummerNormIndex.CyclotomicDegree

/-!
# The cyclotomic compositum in Lemma VII.6.1

This file constructs the actual fields in Milne's square.  Starting from a
cyclic Galois extension `L/K` of prime degree `p`, it embeds both `L` and the
`p`th cyclotomic field in an algebraic closure of `K` and takes their
compositum.  The cyclotomic degree divides `p - 1`, so the two embedded
fields have coprime degrees and are linearly disjoint.
-/

namespace Submission.CField.KNIndex

noncomputable section

universe u

/-- The field-theoretic part of the cyclotomic base-change square. -/
structure CyclotomicCompositumData
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (p : ℕ) where
  K' : Type u
  L' : Type u
  fieldK' : Field K'
  fieldL' : Field L'
  numberFieldK' : NumberField K'
  numberFieldL' : NumberField L'
  algebraKK' : Algebra K K'
  algebraLL' : Algebra L L'
  algebraK'L' : Algebra K' L'
  algebraKL' : Algebra K L'
  scalarTowerKK'L' : IsScalarTower K K' L'
  scalarTowerKLL' : IsScalarTower K L L'
  finiteDimensionalKK' : FiniteDimensional K K'
  finiteDimensionalLL' : FiniteDimensional L L'
  finiteDimensionalK'L' : FiniteDimensional K' L'
  isGaloisKK' : IsGalois K K'
  isGaloisLL' : IsGalois L L'
  isGaloisKL' : IsGalois K L'
  isGaloisK'L' : IsGalois K' L'
  isCyclicK'L' : IsCyclic Gal(L'/K')
  m : ℕ
  primitiveRoot : (primitiveRoots p K').Nonempty
  degreeTop : Module.finrank K' L' = p
  degreeLeft : Module.finrank L L' = m
  degreeRight : Module.finrank K K' = m
  m_dvd_pred : m ∣ p - 1
  galoisRestriction : Gal(L'/K') ≃* Gal(L/K)
  galoisRestriction_commutes : ∀ sigma x,
    algebraMap L L' (galoisRestriction sigma x) =
      sigma (algebraMap L L' x)

/-- A divisor of `p - 1` is coprime to the prime `p`. -/
private theorem coprime_prime_pred
    {m p : ℕ} (hp : p.Prime) (hm : m ∣ p - 1) : p.Coprime m := by
  rw [hp.coprime_iff_not_dvd]
  intro hpm
  have hppred : p ∣ p - 1 := hpm.trans hm
  have hpos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hle : p ≤ p - 1 := Nat.le_of_dvd hpos hppred
  omega

set_option synthInstance.maxHeartbeats 200000 in
-- The compositum carries several transported field and scalar-tower structures.
set_option maxHeartbeats 2000000 in
/-- The compositum `L(ζ_p)` has precisely the degree diagram used in
Lemma VII.6.1. -/
theorem cyclotomic_compositum_data
    (p : ℕ) (hp : p.Prime)
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hdegree : Module.finrank K L = p) :
    Nonempty (CyclotomicCompositumData K L p) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p : K) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  let C := CyclotomicField p K
  letI : IsCyclotomicExtension {p} K C :=
    CyclotomicField.isCyclotomicExtension p K
  letI : FiniteDimensional K C :=
    IsCyclotomicExtension.finiteDimensional {p} K C
  letI : NumberField C := IsCyclotomicExtension.numberField {p} K C
  letI : IsGalois K C := IsCyclotomicExtension.isGalois {p} K C
  let Omega := AlgebraicClosure K
  let eL : L →ₐ[K] Omega := IsAlgClosed.lift
  let eC : C →ₐ[K] Omega := IsAlgClosed.lift
  let A : IntermediateField K Omega := eL.fieldRange
  let B : IntermediateField K Omega := eC.fieldRange
  let M : IntermediateField K Omega := A ⊔ B
  let eLA : L ≃ₐ[K] A := by
    simpa [A, AlgHom.fieldRange_toSubalgebra eL] using
      (AlgEquiv.ofInjectiveField eL)
  let eCB : C ≃ₐ[K] B := by
    simpa [B, AlgHom.fieldRange_toSubalgebra eC] using
      (AlgEquiv.ofInjectiveField eC)
  let A0 : IntermediateField K M := A.restrict le_sup_left
  let B0 : IntermediateField K M := B.restrict le_sup_right
  let eAA0 : A ≃ₐ[K] A0 := IntermediateField.restrict_algEquiv le_sup_left
  let eBB0 : B ≃ₐ[K] B0 := IntermediateField.restrict_algEquiv le_sup_right
  let eLA0 : L ≃ₐ[K] A0 := eLA.trans eAA0
  let eCB0 : C ≃ₐ[K] B0 := eCB.trans eBB0
  letI : FiniteDimensional K A :=
    FiniteDimensional.of_surjective eLA.toLinearEquiv.toLinearMap eLA.surjective
  letI : FiniteDimensional K B :=
    FiniteDimensional.of_surjective eCB.toLinearEquiv.toLinearMap eCB.surjective
  letI : NumberField A := NumberField.of_module_finite K A
  letI : NumberField B := NumberField.of_module_finite K B
  letI : IsGalois K A := IsGalois.of_algEquiv eLA
  letI : IsGalois K B := IsGalois.of_algEquiv eCB
  letI : FiniteDimensional K M :=
    IntermediateField.finiteDimensional_sup A B
  letI : NumberField M := NumberField.of_module_finite K M
  letI : IsGalois K M := inferInstance
  letI : FiniteDimensional K A0 :=
    FiniteDimensional.of_surjective eLA0.toLinearEquiv.toLinearMap eLA0.surjective
  letI : FiniteDimensional K B0 :=
    FiniteDimensional.of_surjective eCB0.toLinearEquiv.toLinearMap eCB0.surjective
  letI : NumberField A0 := NumberField.of_module_finite K A0
  letI : NumberField B0 := NumberField.of_module_finite K B0
  letI : IsGalois K A0 := IsGalois.of_algEquiv eLA0
  letI : IsGalois K B0 := IsGalois.of_algEquiv eCB0
  let jL : L →ₐ[K] M :=
    (IntermediateField.inclusion le_sup_left).comp eLA.toAlgHom
  letI : Algebra B0 M := B0.toAlgebra
  letI : Algebra L M := jL.toRingHom.toAlgebra
  letI : IsScalarTower K B0 M := inferInstance
  letI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun x ↦ by
    change (algebraMap K M) x = jL (algebraMap K L x)
    exact (jL.commutes x).symm
  letI : FiniteDimensional B0 M := FiniteDimensional.right K B0 M
  letI : FiniteDimensional L M := FiniteDimensional.right K L M
  letI : IsGalois B0 M := IsGalois.tower_top_of_isGalois K B0 M
  letI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  let m := Module.finrank K B0
  have hAdegree : Module.finrank K A0 = p := by
    rw [← hdegree]
    simpa using eLA0.symm.toLinearEquiv.finrank_eq
  have hBdegree : Module.finrank K B0 = Module.finrank K C := by
    simpa using eCB0.symm.toLinearEquiv.finrank_eq
  have hm_dvd : m ∣ p - 1 := by
    change Module.finrank K B0 ∣ p - 1
    rw [hBdegree]
    exact cyclotomic_dvd_pred hp K C
  have hcop : (Module.finrank K A0).Coprime (Module.finrank K B0) := by
    rw [hAdegree]
    exact coprime_prime_pred hp hm_dvd
  have hdisj : A0.LinearDisjoint B0 :=
    IntermediateField.LinearDisjoint.of_finrank_coprime hcop
  have hsup : A0 ⊔ B0 = ⊤ := by
    rw [← IntermediateField.lift_inj, IntermediateField.lift_top,
      IntermediateField.lift_sup, IntermediateField.lift_restrict le_sup_left,
      IntermediateField.lift_restrict le_sup_right]
  have hMdegree : Module.finrank K M = p * m := by
    calc
      Module.finrank K M =
          Module.finrank K (⊤ : IntermediateField K M) := by
        rw [IntermediateField.finrank_top']
      _ = Module.finrank K (A0 ⊔ B0 : IntermediateField K M) :=
        congrArg (fun F : IntermediateField K M ↦ Module.finrank K F) hsup.symm
      _ = p * m := by rw [hdisj.finrank_sup, hAdegree]
  have hdegreeLeft : Module.finrank L M = m := by
    have htower := Module.finrank_mul_finrank K L M
    rw [hdegree, hMdegree] at htower
    exact Nat.eq_of_mul_eq_mul_left hp.pos htower
  have hmpos : 0 < m := Module.finrank_pos
  have hdegreeTop : Module.finrank B0 M = p := by
    have htower := Module.finrank_mul_finrank K B0 M
    change m * Module.finrank B0 M = Module.finrank K M at htower
    rw [hMdegree] at htower
    apply Nat.eq_of_mul_eq_mul_left hmpos
    simpa [Nat.mul_comm] using htower
  letI : Fact p.Prime := ⟨hp⟩
  have hcyclic : IsCyclic Gal(M/B0) := by
    apply isCyclic_of_prime_card (p := p)
    rw [IsGalois.card_aut_eq_finrank B0 M, hdegreeTop]
  have hroot : (primitiveRoots p B0).Nonempty := by
    let zeta := IsCyclotomicExtension.zeta p K C
    have hzeta : IsPrimitiveRoot zeta p :=
      IsCyclotomicExtension.zeta_spec p K C
    exact ⟨eCB0 zeta,
      (mem_primitiveRoots hp.pos).2
        (hzeta.map_of_injective eCB0.injective)⟩
  let restrictionHom : Gal(M/B0) →* Gal(A0/K) :=
    IntermediateField.restrictRestrictAlgEquivMapHom K A0 B0 M
  have hrestrictionBijective : Function.Bijective restrictionHom := ⟨
    IntermediateField.restrictRestrictAlgEquivMapHom_injective A0 B0 hsup,
    IntermediateField.restrictRestrictAlgEquivMapHom_surjective A0 B0
      hdisj.inf_eq_bot⟩
  let restrictionEquiv : Gal(M/B0) ≃* Gal(A0/K) :=
    MulEquiv.ofBijective restrictionHom hrestrictionBijective
  let galoisRestriction : Gal(M/B0) ≃* Gal(L/K) :=
    restrictionEquiv.trans (AlgEquiv.autCongr eLA0).symm
  have galoisRestriction_commutes (sigma : Gal(M/B0)) (x : L) :
      algebraMap L M (galoisRestriction sigma x) =
        sigma (algebraMap L M x) := by
    change ((eLA0 (galoisRestriction sigma x) : A0) : M) =
      sigma ((eLA0 x : A0) : M)
    have he : eLA0 (galoisRestriction sigma x) =
        restrictionEquiv sigma (eLA0 x) := by
      simp [galoisRestriction]
    rw [he]
    exact IntermediateField.restrictRestrictAlgEquivMapHom_apply
      A0 B0 sigma (eLA0 x)
  exact ⟨{
    K' := B0
    L' := M
    fieldK' := inferInstance
    fieldL' := inferInstance
    numberFieldK' := inferInstance
    numberFieldL' := inferInstance
    algebraKK' := inferInstance
    algebraLL' := inferInstance
    algebraK'L' := inferInstance
    algebraKL' := inferInstance
    scalarTowerKK'L' := inferInstance
    scalarTowerKLL' := inferInstance
    finiteDimensionalKK' := inferInstance
    finiteDimensionalLL' := inferInstance
    finiteDimensionalK'L' := inferInstance
    isGaloisKK' := inferInstance
    isGaloisLL' := inferInstance
    isGaloisKL' := inferInstance
    isGaloisK'L' := inferInstance
    isCyclicK'L' := hcyclic
    m := m
    primitiveRoot := hroot
    degreeTop := hdegreeTop
    degreeLeft := hdegreeLeft
    degreeRight := rfl
    m_dvd_pred := hm_dvd
    galoisRestriction := galoisRestriction
    galoisRestriction_commutes := galoisRestriction_commutes }⟩

end

end Submission.CField.KNIndex
